/**
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 * <p>
 * http://www.apache.org/licenses/LICENSE-2.0
 * <p>
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.zookeeper.server.quorum;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.net.Socket;
import java.nio.ByteBuffer;
import java.util.Iterator;
import java.util.Queue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.ReadLock;

import javax.security.sasl.SaslException;

import org.apache.jute.BinaryInputArchive;
import org.apache.jute.BinaryOutputArchive;
import org.apache.zookeeper.KeeperException.SessionExpiredException;
import org.apache.zookeeper.ZooDefs.OpCode;
import org.apache.zookeeper.server.Request;
import org.apache.zookeeper.server.TxnLogProposalIterator;
import org.apache.zookeeper.server.ZKDatabase;
import org.apache.zookeeper.server.ZooKeeperThread;
import org.apache.zookeeper.server.ZooTrace;
import org.apache.zookeeper.server.quorum.Leader.Proposal;
import org.apache.zookeeper.server.quorum.QuorumPeer.LearnerType;
import org.apache.zookeeper.server.util.SerializeUtils;
import org.apache.zookeeper.server.util.ZxidUtils;
import org.apache.zookeeper.txn.TxnHeader;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * There will be an instance of this class created by the Leader for each
 * learner. All communication with a learner is handled by this
 * class.
 */
public class LearnerHandler extends ZooKeeperThread {
    private static final Logger LOG = LoggerFactory.getLogger(LearnerHandler.class);

    protected final Socket sock;

    public Socket getSocket() {
        return sock;
    }

    final Leader leader;

    /**
     * Deadline for receiving the next ack. If we are bootstrapping then
     * it's based on the initLimit, if we are done bootstrapping it's based
     * on the syncLimit. Once the deadline is past this learner should
     * be considered no longer "sync'd" with the leader.
     */
    volatile long tickOfNextAckDeadline;

    /**
     * ZooKeeper server identifier of this learner
     */
    protected long sid = 0;

    long getSid() {
        return sid;
    }

    protected int version = 0x1;

    int getVersion() {
        return version;
    }

    /**
     * The packets to be sent to the learner
     */
    final LinkedBlockingQueue<QuorumPacket> queuedPackets =
            new LinkedBlockingQueue<QuorumPacket>();

    /**
     * This class controls the time that the Leader has been
     * waiting for acknowledgement of a proposal from this Learner.
     * If the time is above syncLimit, the connection will be closed.
     * It keeps track of only one proposal at a time, when the ACK for
     * that proposal arrives, it switches to the last proposal received
     * or clears the value if there is no pending proposal.
     */
    private class SyncLimitCheck {
        private boolean started = false;
        private long currentZxid = 0;//最久一次更新了但是没有收到ack的proposal的zxid
        private long currentTime = 0;//最久一次更新了但是没有收到ack的proposal的时间
        private long nextZxid = 0;//最新一次更新了但是没有收到ack的proposal的zxid
        private long nextTime = 0;//最新一次更新了但是没有收到ack的proposal的时间

        public synchronized void start() {
            started = true;
        }

        //发送proposal时，更新提议的统计时间
        public synchronized void updateProposal(long zxid, long time) {
            if (!started) {
                return;
            }
            if (currentTime == 0) {
                currentTime = time;
                currentZxid = zxid;
            } else {
                nextTime = time;
                nextZxid = zxid;
            }
        }

        //收到Learner关于zxid的ack了，更新ack的统计时间
        public synchronized void updateAck(long zxid) {
            if (currentZxid == zxid) {//如果是刚刚发送的ack
                currentTime = nextTime;//传递到下一个记录
                currentZxid = nextZxid;
                nextTime = 0;
                nextZxid = 0;
            } else if (nextZxid == zxid) {//如果旧的ack还没收到 但是收到了 新的ack
                LOG.warn("ACK for " + zxid + " received before ACK for " + currentZxid + "!!!!");
                nextTime = 0;
                nextZxid = 0;
            }
        }

        public synchronized boolean check(long time) {//如果没有等待超时，返回true
            if (currentTime == 0) {
                return true;
            } else {
                long msDelay = (time - currentTime) / 1000000;//当前时间与最久一次没收到ack的proposal的时间差
                return (msDelay < (leader.self.tickTime * leader.self.syncLimit));
            }
        }
    }

    ;

    private SyncLimitCheck syncLimitCheck = new SyncLimitCheck();

    private BinaryInputArchive ia;

    private BinaryOutputArchive oa;

    private final BufferedInputStream bufferedInput;
    private BufferedOutputStream bufferedOutput;

    /**
     * Keep track of whether we have started send packets thread
     */
    private volatile boolean sendingThreadStarted = false;

    /**
     * For testing purpose, force leader to use snapshot to sync with followers
     */
    public static final String FORCE_SNAP_SYNC = "zookeeper.forceSnapshotSync";
    private boolean forceSnapSync = false;

    /**
     * Keep track of whether we need to queue TRUNC or DIFF into packet queue
     * that we are going to blast it to the learner
     */
    private boolean needOpPacket = true;

    /**
     * Last zxid sent to the learner as part of synchronization
     */
    private long leaderLastZxid;

    LearnerHandler(Socket sock, BufferedInputStream bufferedInput, Leader leader) throws IOException {
        super("LearnerHandler-" + sock.getRemoteSocketAddress());
        this.sock = sock;
        this.leader = leader;
        this.bufferedInput = bufferedInput;

        if (Boolean.getBoolean(FORCE_SNAP_SYNC)) {
            forceSnapSync = true;
            LOG.info("Forcing snapshot sync is enabled");
        }

        try {
            if (leader.self != null) {
                leader.self.authServer.authenticate(sock,
                        new DataInputStream(bufferedInput));
            }
        } catch (IOException e) {
            LOG.error("Server failed to authenticate quorum learner, addr: {}, closing connection",
                    sock.getRemoteSocketAddress(), e);
            try {
                sock.close();
            } catch (IOException ie) {
                LOG.error("Exception while closing socket", ie);
            }
            throw new SaslException("Authentication failure: " + e.getMessage());
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("LearnerHandler ").append(sock);
        sb.append(" tickOfNextAckDeadline:").append(tickOfNextAckDeadline());
        sb.append(" synced?:").append(synced());
        sb.append(" queuedPacketLength:").append(queuedPackets.size());
        return sb.toString();
    }

    /**
     * If this packet is queued, the sender thread will exit
     */
    final QuorumPacket proposalOfDeath = new QuorumPacket();

    private LearnerType learnerType = LearnerType.PARTICIPANT;

    public LearnerType getLearnerType() {
        return learnerType;
    }

    /**
     * This method will use the thread to send packets added to the
     * queuedPackets list
     *
     * @throws InterruptedException
     */
    private void sendPackets() throws InterruptedException {
        long traceMask = ZooTrace.SERVER_PACKET_TRACE_MASK;
        while (true) {
            try {
                QuorumPacket p;
                p = queuedPackets.poll();
                if (p == null) {
                    bufferedOutput.flush();
                    p = queuedPackets.take();
                }

                if (p == proposalOfDeath) {
                    // Packet of death!
                    break;
                }
                if (p.getType() == Leader.PING) {
                    traceMask = ZooTrace.SERVER_PING_TRACE_MASK;
                }
                if (p.getType() == Leader.PROPOSAL) {
                    syncLimitCheck.updateProposal(p.getZxid(), System.nanoTime());
                }
                if (LOG.isTraceEnabled()) {
                    ZooTrace.logQuorumPacket(LOG, traceMask, 'o', p);
                }
                oa.writeRecord(p, "packet");
            } catch (IOException e) {
                if (!sock.isClosed()) {
                    LOG.warn("Unexpected exception at " + this, e);
                    try {
                        // this will cause everything to shutdown on
                        // this learner handler and will help notify
                        // the learner/observer instantaneously
                        sock.close();
                    } catch (IOException ie) {
                        LOG.warn("Error closing socket for handler " + this, ie);
                    }
                }
                break;
            }
        }
    }

    static public String packetToString(QuorumPacket p) {
        String type;
        String mess = null;

        switch (p.getType()) {
            case Leader.ACK:
                type = "ACK";
                break;
            case Leader.COMMIT:
                type = "COMMIT";
                break;
            case Leader.FOLLOWERINFO:
                type = "FOLLOWERINFO";
                break;
            case Leader.NEWLEADER:
                type = "NEWLEADER";
                break;
            case Leader.PING:
                type = "PING";
                break;
            case Leader.PROPOSAL:
                type = "PROPOSAL";
                TxnHeader hdr = new TxnHeader();
                try {
                    SerializeUtils.deserializeTxn(p.getData(), hdr);
                    // mess = "transaction: " + txn.toString();
                } catch (IOException e) {
                    LOG.warn("Unexpected exception", e);
                }
                break;
            case Leader.REQUEST:
                type = "REQUEST";
                break;
            case Leader.REVALIDATE:
                type = "REVALIDATE";
                ByteArrayInputStream bis = new ByteArrayInputStream(p.getData());
                DataInputStream dis = new DataInputStream(bis);
                try {
                    long id = dis.readLong();
                    mess = " sessionid = " + id;
                } catch (IOException e) {
                    LOG.warn("Unexpected exception", e);
                }

                break;
            case Leader.UPTODATE:
                type = "UPTODATE";
                break;
            case Leader.DIFF:
                type = "DIFF";
                break;
            case Leader.TRUNC:
                type = "TRUNC";
                break;
            case Leader.SNAP:
                type = "SNAP";
                break;
            case Leader.ACKEPOCH:
                type = "ACKEPOCH";
                break;
            case Leader.SYNC:
                type = "SYNC";
                break;
            case Leader.INFORM:
                type = "INFORM";
                break;
            case Leader.COMMITANDACTIVATE:
                type = "COMMITANDACTIVATE";
                break;
            case Leader.INFORMANDACTIVATE:
                type = "INFORMANDACTIVATE";
                break;
            default:
                type = "UNKNOWN" + p.getType();
        }
        String entry = null;
        if (type != null) {
            entry = type + " " + Long.toHexString(p.getZxid()) + " " + mess;
        }
        return entry;
    }

    /**
     * This thread will receive packets from the peer and process them and
     * also listen to new connections from new peers.
     */
    @Override
    public void run() {
        try {
            /*
             * leader与folower建立连接后, 新建一个LearnerHandler线程与folower通信
             */

            /*
             * 把自己加入leader维护的learnerHandler列表中,
             * leader主线程会周期性的ping各folower, 在ping的过程中检查folower是否超时,
             * 详见leader的主线程
             */
            leader.addLearnerHandler(this);
            tickOfNextAckDeadline = leader.self.tick.get()
                    + leader.self.initLimit + leader.self.syncLimit;

            ia = BinaryInputArchive.getArchive(bufferedInput);
            bufferedOutput = new BufferedOutputStream(sock.getOutputStream());
            oa = BinaryOutputArchive.getArchive(bufferedOutput);

            QuorumPacket qp = new QuorumPacket();
            ia.readRecord(qp, "packet");

            /*
             * 与folower建立连接后, folower首先发送FOLOWERINFO消息,
             * 消息内包含folower的lastZxid, 用于生成新的epoch
             * 此处folower的lastZxid并不是用于决定数据同步类型的
             */
            if (qp.getType() != Leader.FOLLOWERINFO && qp.getType() != Leader.OBSERVERINFO) {
                LOG.error("First packet " + qp.toString()
                        + " is not FOLLOWERINFO or OBSERVERINFO!");
                return;
            }

            byte learnerInfoData[] = qp.getData();
            if (learnerInfoData != null) {
                ByteBuffer bbsid = ByteBuffer.wrap(learnerInfoData);
                if (learnerInfoData.length >= 8) {
                    this.sid = bbsid.getLong();
                }
                if (learnerInfoData.length >= 12) {
                    this.version = bbsid.getInt(); // protocolVersion
                }
                if (learnerInfoData.length >= 20) {
                    long configVersion = bbsid.getLong();
                    if (configVersion > leader.self.getQuorumVerifier().getVersion()) {
                        throw new IOException("Follower is ahead of the leader (has a later activated configuration)");
                    }
                }
            } else {
                this.sid = leader.followerCounter.getAndDecrement();
            }

            if (leader.self.getView().containsKey(this.sid)) {
                LOG.info("Follower sid: " + this.sid + " : info : "
                        + leader.self.getView().get(this.sid).toString());
            } else {
                LOG.info("Follower sid: " + this.sid + " not in the current config " + Long.toHexString(leader.self.getQuorumVerifier().getVersion()));
            }

            if (qp.getType() == Leader.OBSERVERINFO) {
                learnerType = LearnerType.OBSERVER;
            }

            long lastAcceptedEpoch = ZxidUtils.getEpochFromZxid(qp.getZxid());

            long peerLastZxid;
            StateSummary ss = null;
            long zxid = qp.getZxid();

            /*
             * leader生成新的epoch, 新的epoch = max{多于半数folower的epoch} + 1
             */
            long newEpoch = leader.getEpochToPropose(this.getSid(), lastAcceptedEpoch);

            /*
             * 生成新的lastZxid
             */
            long newLeaderZxid = ZxidUtils.makeZxid(newEpoch, 0);

            if (this.getVersion() < 0x10000) {
                // we are going to have to extrapolate the epoch information
                long epoch = ZxidUtils.getEpochFromZxid(zxid);
                ss = new StateSummary(epoch, zxid);
                // fake the message
                leader.waitForEpochAck(this.getSid(), ss);
            } else {
                byte ver[] = new byte[4];
                ByteBuffer.wrap(ver).putInt(0x10000);
                /*
                 * 发送LEADERINFO信息, 包含自己的lastZxid
                 */
                QuorumPacket newEpochPacket = new QuorumPacket(Leader.LEADERINFO, newLeaderZxid, ver, null);
                oa.writeRecord(newEpochPacket, "packet");
                bufferedOutput.flush();
                QuorumPacket ackEpochPacket = new QuorumPacket();


                /*
                 * folower收到LEADERINFO响应消息为ACKEPOCH消息
                 */
                ia.readRecord(ackEpochPacket, "packet");
                if (ackEpochPacket.getType() != Leader.ACKEPOCH) {
                    LOG.error(ackEpochPacket.toString()
                            + " is not ACKEPOCH");
                    return;
                }
                ByteBuffer bbepoch = ByteBuffer.wrap(ackEpochPacket.getData());
                ss = new StateSummary(bbepoch.getInt(), ackEpochPacket.getZxid());

                /*
                 * 阻塞等待过半数的folower返回ACKEPOCH消息
                 */
                leader.waitForEpochAck(this.getSid(), ss);
            }

            /*
             * 获取folower的lastZxid, 此处的lastZxid用于决定数据的同步类型
             */
            peerLastZxid = ss.getLastZxid();

            // Take any necessary action if we need to send TRUNC or DIFF
            // startForwarding() will be called in all cases

            /*
             * syncFolower用于数据同步:
             * 1. 如果是DIFF和TRUNC类型的数据同步, 则数据同步过程在syncFolower内部做掉, 并返回false
             * 2. 如果是SNAP类型的数据同步, 则在syncFolower外部做, syncFolower会返回true
             */
            boolean needSnap = syncFollower(peerLastZxid, leader.zk.getZKDatabase(), leader);

            /* if we are not truncating or sending a diff just send a snapshot */

            /*
             * 处理SNAP类型的数据同步
             */
            if (needSnap) {
                boolean exemptFromThrottle = getLearnerType() != LearnerType.OBSERVER;
                LearnerSnapshot snapshot =
                        leader.getLearnerSnapshotThrottler().beginSnapshot(exemptFromThrottle);
                try {
                    long zxidToSend = leader.zk.getZKDatabase().getDataTreeLastProcessedZxid();
                    oa.writeRecord(new QuorumPacket(Leader.SNAP, zxidToSend, null, null), "packet");
                    bufferedOutput.flush();

                    LOG.info("Sending snapshot last zxid of peer is 0x{}, zxid of leader is 0x{}, "
                                    + "send zxid of db as 0x{}, {} concurrent snapshots, "
                                    + "snapshot was {} from throttle",
                            Long.toHexString(peerLastZxid),
                            Long.toHexString(leaderLastZxid),
                            Long.toHexString(zxidToSend),
                            snapshot.getConcurrentSnapshotNumber(),
                            snapshot.isEssential() ? "exempt" : "not exempt");
                    // Dump data to peer
                    leader.zk.getZKDatabase().serializeSnapshot(oa);
                    oa.writeString("BenWasHere", "signature");
                    bufferedOutput.flush();
                } finally {
                    snapshot.close();
                }
            }

            LOG.debug("Sending NEWLEADER message to " + sid);
            // the version of this quorumVerifier will be set by leader.lead() in case
            // the leader is just being established. waitForEpochAck makes sure that readyToStart is true if
            // we got here, so the version was set

            /*
             * folower数据同步完成后发送NEWLEADER消息包, 标志着自己数据同步的完成
             */
            if (getVersion() < 0x10000) {
                QuorumPacket newLeaderQP = new QuorumPacket(Leader.NEWLEADER,
                        newLeaderZxid, null, null);
                oa.writeRecord(newLeaderQP, "packet");
            } else {
                QuorumPacket newLeaderQP = new QuorumPacket(Leader.NEWLEADER,
                        newLeaderZxid, leader.self.getLastSeenQuorumVerifier()
                        .toString().getBytes(), null);
                queuedPackets.add(newLeaderQP);
            }
            bufferedOutput.flush();

            // Start thread that blast packets in the queue to learner

            /*
             * DIFF和TRUNC的数据同步只是把数据放在了Queue里边, 这里真正的发送packet
             */
            startSendingPackets();

            /*
             * Have to wait for the first ACK, wait until
             * the leader is ready, and only then we can
             * start processing messages.
             */
            qp = new QuorumPacket();
            ia.readRecord(qp, "packet");
            if (qp.getType() != Leader.ACK) {
                LOG.error("Next packet was supposed to be an ACK,"
                        + " but received packet: {}", packetToString(qp));
                return;
            }

            if (LOG.isDebugEnabled()) {
                LOG.debug("Received NEWLEADER-ACK message from " + sid);
            }
            /*
             * 阻塞等待至大部分的folower完成数据同步
             */
            leader.waitForNewLeaderAck(getSid(), qp.getZxid());

            /*
             * syncLimitCheck线程用于leader检查folower的Proposol是否在超时范围内发送了ACK
             * 如果没有, leader会主动关闭与该folower的learnerHandler线程, 并认为该节点宕机
             * 此处只是启动了检查的线程, 真正的减产在leader的主线程周期性发ping的时候做, 详见leader主线程
             */
            syncLimitCheck.start();

            // now that the ack has been processed expect the syncLimit
            /*
             * leader与folower长连接的超时时间, 超时断开, folower返回looking状态
             */
            sock.setSoTimeout(leader.self.tickTime * leader.self.syncLimit);

            /*
             * Wait until leader starts up
             */
            synchronized (leader.zk) {
                while (!leader.zk.isRunning() && !this.isInterrupted()) {
                    leader.zk.wait(20);
                }
            }
            // Mutation packets will be queued during the serialize,
            // so we need to mark when the peer can actually start
            // using the data
            //
            LOG.debug("Sending UPTODATE message to " + sid);

            /*
             * 发送UPTODATE包, 告诉folower你数据已经和leader一样新了
             * folower在收到UPTODATE包后, 事实上只是打印了一条日志, 并没有额外响应
             */
            queuedPackets.add(new QuorumPacket(Leader.UPTODATE, -1, null, null));

            /*
             * 数据同步完成, 进入broadcast阶段
             */
            while (true) {
                qp = new QuorumPacket();
                ia.readRecord(qp, "packet");

                long traceMask = ZooTrace.SERVER_PACKET_TRACE_MASK;
                if (qp.getType() == Leader.PING) {
                    traceMask = ZooTrace.SERVER_PING_TRACE_MASK;
                }
                if (LOG.isTraceEnabled()) {
                    ZooTrace.logQuorumPacket(LOG, traceMask, 'i', qp);
                }
                tickOfNextAckDeadline = leader.self.tick.get() + leader.self.syncLimit;


                ByteBuffer bb;
                long sessionId;
                int cxid;
                int type;

                switch (qp.getType()) {
                    case Leader.ACK:
                        if (this.learnerType == LearnerType.OBSERVER) {
                            if (LOG.isDebugEnabled()) {
                                LOG.debug("Received ACK from Observer  " + this.sid);
                            }
                        }
                        syncLimitCheck.updateAck(qp.getZxid());
                        leader.processAck(this.sid, qp.getZxid(), sock.getLocalSocketAddress());
                        break;
                    /*
                     * ping消息携带了folower的session信息
                     */
                    case Leader.PING:
                        // Process the touches
                        ByteArrayInputStream bis = new ByteArrayInputStream(qp
                                .getData());
                        DataInputStream dis = new DataInputStream(bis);
                        while (dis.available() > 0) {
                            long sess = dis.readLong();
                            int to = dis.readInt();
                            leader.zk.touch(sess, to);
                        }
                        break;
                    case Leader.REVALIDATE:
                        bis = new ByteArrayInputStream(qp.getData());
                        dis = new DataInputStream(bis);
                        long id = dis.readLong();
                        int to = dis.readInt();
                        ByteArrayOutputStream bos = new ByteArrayOutputStream();
                        DataOutputStream dos = new DataOutputStream(bos);
                        dos.writeLong(id);
                        boolean valid = leader.zk.checkIfValidGlobalSession(id, to);
                        if (valid) {
                            try {
                                //set the session owner
                                // as the follower that
                                // owns the session
                                leader.zk.setOwner(id, this);
                            } catch (SessionExpiredException e) {
                                LOG.error("Somehow session " + Long.toHexString(id) +
                                        " expired right after being renewed! (impossible)", e);
                            }
                        }
                        if (LOG.isTraceEnabled()) {
                            ZooTrace.logTraceMessage(LOG,
                                    ZooTrace.SESSION_TRACE_MASK,
                                    "Session 0x" + Long.toHexString(id)
                                            + " is valid: " + valid);
                        }
                        dos.writeBoolean(valid);
                        qp.setData(bos.toByteArray());
                        queuedPackets.add(qp);
                        break;
                    case Leader.REQUEST:
                        bb = ByteBuffer.wrap(qp.getData());
                        sessionId = bb.getLong();
                        cxid = bb.getInt();
                        type = bb.getInt();
                        bb = bb.slice();
                        Request si;
                        if (type == OpCode.sync) {
                            si = new LearnerSyncRequest(this, sessionId, cxid, type, bb, qp.getAuthinfo());
                        } else {
                            si = new Request(null, sessionId, cxid, type, bb, qp.getAuthinfo());
                        }
                        si.setOwner(this);
                        leader.zk.submitLearnerRequest(si);
                        break;
                    default:
                        LOG.warn("unexpected quorum packet, type: {}", packetToString(qp));
                        break;
                }
            }
        } catch (IOException e) {
            if (sock != null && !sock.isClosed()) {
                LOG.error("Unexpected exception causing shutdown while sock "
                        + "still open", e);
                //close the socket to make sure the
                //other side can see it being close
                try {
                    sock.close();
                } catch (IOException ie) {
                    // do nothing
                }
            }
        } catch (InterruptedException e) {
            LOG.error("Unexpected exception causing shutdown", e);
        } catch (SnapshotThrottleException e) {
            LOG.error("too many concurrent snapshots: " + e);
        } finally {
            LOG.warn("******* GOODBYE "
                    + (sock != null ? sock.getRemoteSocketAddress() : "<null>")
                    + " ********");
            shutdown();
        }
    }

    /**
     * Start thread that will forward any packet in the queue to the follower
     */
    protected void startSendingPackets() {
        if (!sendingThreadStarted) {
            // Start sending packets
            new Thread() {
                public void run() {
                    Thread.currentThread().setName(
                            "Sender-" + sock.getRemoteSocketAddress());
                    try {
                        sendPackets();
                    } catch (InterruptedException e) {
                        LOG.warn("Unexpected interruption " + e.getMessage());
                    }
                }
            }.start();
            sendingThreadStarted = true;
        } else {
            LOG.error("Attempting to start sending thread after it already started");
        }
    }

    /**
     * Determine if we need to sync with follower using DIFF/TRUNC/SNAP
     * and setup follower to receive packets from commit processor
     *
     * @param peerLastZxid
     * @param db
     * @param leader
     * @return true if snapshot transfer is needed.
     */
    public boolean syncFollower(long peerLastZxid, ZKDatabase db, Leader leader) {
        /*
         * When leader election is completed, the leader will set its
         * lastProcessedZxid to be (epoch < 32). There will be no txn associated
         * with this zxid.
         *
         * The learner will set its lastProcessedZxid to the same value if
         * it get DIFF or SNAP from the leader. If the same learner come
         * back to sync with leader using this zxid, we will never find this
         * zxid in our history. In this case, we will ignore TRUNC logic and
         * always send DIFF if we have old enough history
         */
        boolean isPeerNewEpochZxid = (peerLastZxid & 0xffffffffL) == 0;
        // Keep track of the latest zxid which already queued
        long currentZxid = peerLastZxid;
        boolean needSnap = true;
        boolean txnLogSyncEnabled = db.isTxnLogSyncEnabled();
        ReentrantReadWriteLock lock = db.getLogLock();

        /*
         * 这里需要获取db的读锁, 分两种情况讨论这个读锁的利弊:
         * 1. 就是在选举刚完成, 处于Recovery Phase, Brocast Phase还没开始, 这种情况, 这个读锁是没有太大的弊端的
         * 2. 已经处于Boradcast Phase, 某个宕机的folower突然恢复, 加入集群, 恢复数据, 这时,
         * 这个读锁会导致leader暂时无法处理更新请求
         */
        ReadLock rl = lock.readLock();
        try {
            rl.lock();

            /*
             * maxCommittedLog: 内存中包含的最大committed log的zxid
             * minCommittedLog: 内存中包含的最新的committed log的zxid
             * lastProcessedZxid: leader接收的最新的log的zxid, 该log可能没有commit
             */
            long maxCommittedLog = db.getmaxCommittedLog();
            long minCommittedLog = db.getminCommittedLog();
            long lastProcessedZxid = db.getDataTreeLastProcessedZxid();

            LOG.info("Synchronizing with Follower sid: {} maxCommittedLog=0x{}"
                            + " minCommittedLog=0x{} lastProcessedZxid=0x{}"
                            + " peerLastZxid=0x{}", getSid(),
                    Long.toHexString(maxCommittedLog),
                    Long.toHexString(minCommittedLog),
                    Long.toHexString(lastProcessedZxid),
                    Long.toHexString(peerLastZxid));

            if (db.getCommittedLog().isEmpty()) {
                /*
                 * It is possible that committedLog is empty. In that case
                 * setting these value to the latest txn in leader db
                 * will reduce the case that we need to handle
                 *
                 * Here is how each case handle by the if block below
                 * 1. lastProcessZxid == peerZxid -> Handle by (2)
                 * 2. lastProcessZxid < peerZxid -> Handle by (3)
                 * 3. lastProcessZxid > peerZxid -> Handle by (5)
                 */
                minCommittedLog = lastProcessedZxid;
                maxCommittedLog = lastProcessedZxid;
            }

            /*
             * Here are the cases that we want to handle
             *
             * 1. Force sending snapshot (for testing purpose)
             * 2. Peer and leader is already sync, send empty diff
             * 3. Follower has txn that we haven't seen. This may be old leader
             *    so we need to send TRUNC. However, if peer has newEpochZxid,
             *    we cannot send TRUNC since the follower has no txnlog
             * 4. Follower is within committedLog range or already in-sync.
             *    We may need to send DIFF or TRUNC depending on follower's zxid
             *    We always send empty DIFF if follower is already in-sync
             * 5. Follower missed the committedLog. We will try to use on-disk
             *    txnlog + committedLog to sync with follower. If that fail,
             *    we will send snapshot
             */

            /*
             * 测试用
             */
            if (forceSnapSync) {
                // Force leader to use snapshot to sync with follower
                LOG.warn("Forcing snapshot sync - should not see this in production");
                /*
                 * folower的lastZxid和leader的lasrProcessedZxid相同, 说明folower和leader数据完全一致,
                 * (包括那个还没commit的log都是一致的), 发送空DIFF
                 */
            } else if (lastProcessedZxid == peerLastZxid) {
                // Follower is already sync with us, send empty diff
                LOG.info("Sending DIFF zxid=0x" + Long.toHexString(peerLastZxid) +
                        " for peer sid: " + getSid());
                queueOpPacket(Leader.DIFF, peerLastZxid);
                needOpPacket = false;
                needSnap = false;
                /*
                 * folower的lastZxid比leader已经提交的最大log的zxid还大, 发送TRUNC包和maxCommittedLog给folower
                 * isPeerNewEpochZxid这个flag是一种特殊case的处理:
                 * 1. 正常流程中, isPeerNewEpochZxid一定是false
                 * 2. 如果某个folower完成同步后挂了重启又进行数据同步, isPeerNewEpochZxid会变成true, 对这种case进行特殊处理
                 */
            } else if (peerLastZxid > maxCommittedLog && !isPeerNewEpochZxid) {
                // Newer than committedLog, send trunc and done
                LOG.debug("Sending TRUNC to follower zxidToSend=0x" +
                        Long.toHexString(maxCommittedLog) +
                        " for peer sid:" + getSid());
                queueOpPacket(Leader.TRUNC, maxCommittedLog);
                currentZxid = maxCommittedLog;
                needOpPacket = false;
                needSnap = false;
                /*
                 * folower的lastZxid在leader的内存记录中
                 */
            } else if ((maxCommittedLog >= peerLastZxid)
                    && (minCommittedLog <= peerLastZxid)) {
                // Follower is within commitLog range
                LOG.info("Using committedLog for peer sid: " + getSid());
                Iterator<Proposal> itr = db.getCommittedLog().iterator();

                //Queue committed proposals into packet queue. The range of packets which
                //is going to be queued are (peerLaxtZxid, maxZxid]
                currentZxid = queueCommittedProposals(itr, peerLastZxid,
                        null, maxCommittedLog);
                needSnap = false;
                /*
                 * folower的lastZxid在内存中已经找不到
                 */
            } else if (peerLastZxid < minCommittedLog && txnLogSyncEnabled) {
                // Use txnlog and committedLog to sync

                // Calculate sizeLimit that we allow to retrieve txnlog from disk

                /*
                 * 用户可以配置阈值, 超过这个阈值则直接发送snap进行同步, 低于这个阈值则从snap读取Proposol进行同步
                 * 阈值默认是snap总大小的0.33
                 */
                long sizeLimit = db.calculateTxnLogSizeLimit();
                // This method can return empty iterator if the requested zxid
                // is older than on-disk txnlog

                /*
                 * getProposalsFromTxnLog如果返回
                 * 1. 空迭代器, 代表snap同步机制
                 * 2. 非空迭代器, 则类似组个发送Proposal和Commit
                 * 3. sizelimit为负数则代表全部采用snap同步机制
                 */
                Iterator<Proposal> txnLogItr = db.getProposalsFromTxnLog(
                        peerLastZxid, sizeLimit);
                if (txnLogItr.hasNext()) {
                    LOG.info("Use txnlog and committedLog for peer sid: " + getSid());

                    /*
                     * 分两步分别发送所有的Proposql, 为什么分两步?
                     * 1. (peerLastZxid, minCommittedLog]区间的Proposal在硬盘中
                     * 2. minCommitedLog之后所有的Proposal在内存中
                     */

                    /*
                     * 发送(peerLastZxid, minCommittedLog]这个区间的Proposal
                     */
                    currentZxid = queueCommittedProposals(txnLogItr, peerLastZxid,
                            minCommittedLog, maxCommittedLog);

                    LOG.debug("Queueing committedLog 0x" + Long.toHexString(currentZxid));
                    Iterator<Proposal> committedLogItr = db.getCommittedLog().iterator();

                    /*
                     * 发送minCommitedLog之后所有的Proposql
                     */
                    currentZxid = queueCommittedProposals(committedLogItr, currentZxid,
                            null, maxCommittedLog);
                    needSnap = false;
                }
                // closing the resources
                if (txnLogItr instanceof TxnLogProposalIterator) {
                    TxnLogProposalIterator txnProposalItr = (TxnLogProposalIterator) txnLogItr;
                    txnProposalItr.close();
                }
            } else {
                LOG.warn("Unhandled scenario for peer sid: {} maxCommittedLog=0x{}"
                                + " minCommittedLog=0x{} lastProcessedZxid=0x{}"
                                + " peerLastZxid=0x{} txnLogSyncEnabled={}", getSid(),
                        Long.toHexString(maxCommittedLog),
                        Long.toHexString(minCommittedLog),
                        Long.toHexString(lastProcessedZxid),
                        Long.toHexString(peerLastZxid),
                        txnLogSyncEnabled);
            }
            LOG.debug("Start forwarding 0x" + Long.toHexString(currentZxid) +
                    " for peer sid: " + getSid());
            leaderLastZxid = leader.startForwarding(this, currentZxid);
        } finally {
            rl.unlock();
        }

        if (needOpPacket && !needSnap) {
            // This should never happen, but we should fall back to sending
            // snapshot just in case.
            LOG.error("Unhandled scenario for peer sid: " + getSid() +
                    " fall back to use snapshot");
            needSnap = true;
        }

        /*
         * needSnap返回值默认为true
         */
        return needSnap;
    }

    /**
     * Queue committed proposals into packet queue. The range of packets which
     * is going to be queued are (peerLaxtZxid, maxZxid]
     *
     * @param itr               iterator point to the proposals
     * @param peerLastZxid      last zxid seen by the follower
     * @param maxZxid           max zxid of the proposal to queue, null if no limit
     * @param lastCommittedZxid when sending diff, we need to send lastCommittedZxid
     *                          on the leader to follow Zab 1.0 protocol.
     * @return last zxid of the queued proposal
     */
    protected long queueCommittedProposals(Iterator<Proposal> itr,
                                           long peerLastZxid, Long maxZxid, Long lastCommittedZxid) {
        boolean isPeerNewEpochZxid = (peerLastZxid & 0xffffffffL) == 0;
        long queuedZxid = peerLastZxid;
        // as we look through proposals, this variable keeps track of previous
        // proposal Id.
        long prevProposalZxid = -1;
        while (itr.hasNext()) {
            Proposal propose = itr.next();

            long packetZxid = propose.packet.getZxid();
            // abort if we hit the limit
            if ((maxZxid != null) && (packetZxid > maxZxid)) {
                break;
            }

            // skip the proposals the peer already has
            if (packetZxid < peerLastZxid) {
                prevProposalZxid = packetZxid;
                continue;
            }

            // If we are sending the first packet, figure out whether to trunc
            // or diff
            if (needOpPacket) {

                // Send diff when we see the follower's zxid in our history
                if (packetZxid == peerLastZxid) {
                    LOG.info("Sending DIFF zxid=0x" +
                            Long.toHexString(lastCommittedZxid) +
                            " for peer sid: " + getSid());
                    queueOpPacket(Leader.DIFF, lastCommittedZxid);
                    needOpPacket = false;
                    continue;
                }

                if (isPeerNewEpochZxid) {
                    // Send diff and fall through if zxid is of a new-epoch
                    LOG.info("Sending DIFF zxid=0x" +
                            Long.toHexString(lastCommittedZxid) +
                            " for peer sid: " + getSid());
                    queueOpPacket(Leader.DIFF, lastCommittedZxid);
                    needOpPacket = false;
                } else if (packetZxid > peerLastZxid) {
                    // Peer have some proposals that the leader hasn't seen yet
                    // it may used to be a leader
                    if (ZxidUtils.getEpochFromZxid(packetZxid) !=
                            ZxidUtils.getEpochFromZxid(peerLastZxid)) {
                        // We cannot send TRUNC that cross epoch boundary.
                        // The learner will crash if it is asked to do so.
                        // We will send snapshot this those cases.
                        LOG.warn("Cannot send TRUNC to peer sid: " + getSid() +
                                " peer zxid is from different epoch");
                        return queuedZxid;
                    }

                    LOG.info("Sending TRUNC zxid=0x" +
                            Long.toHexString(prevProposalZxid) +
                            " for peer sid: " + getSid());
                    queueOpPacket(Leader.TRUNC, prevProposalZxid);
                    needOpPacket = false;
                }
            }

            if (packetZxid <= queuedZxid) {
                // We can get here, if we don't have op packet to queue
                // or there is a duplicate txn in a given iterator
                continue;
            }

            // Since this is already a committed proposal, we need to follow
            // it by a commit packet
            queuePacket(propose.packet);
            queueOpPacket(Leader.COMMIT, packetZxid);
            queuedZxid = packetZxid;

        }

        if (needOpPacket && isPeerNewEpochZxid) {
            // We will send DIFF for this kind of zxid in any case. This if-block
            // is the catch when our history older than learner and there is
            // no new txn since then. So we need an empty diff
            LOG.info("Sending DIFF zxid=0x" +
                    Long.toHexString(lastCommittedZxid) +
                    " for peer sid: " + getSid());
            queueOpPacket(Leader.DIFF, lastCommittedZxid);
            needOpPacket = false;
        }

        return queuedZxid;
    }

    public void shutdown() {
        // Send the packet of death
        try {
            queuedPackets.put(proposalOfDeath);
        } catch (InterruptedException e) {
            LOG.warn("Ignoring unexpected exception", e);
        }
        try {
            if (sock != null && !sock.isClosed()) {
                sock.close();
            }
        } catch (IOException e) {
            LOG.warn("Ignoring unexpected exception during socket close", e);
        }
        this.interrupt();
        leader.removeLearnerHandler(this);
    }

    public long tickOfNextAckDeadline() {
        return tickOfNextAckDeadline;
    }

    /**
     * ping calls from the leader to the peers
     */
    public void ping() {
        // If learner hasn't sync properly yet, don't send ping packet
        // otherwise, the learner will crash
        if (!sendingThreadStarted) {
            return;
        }
        long id;
        if (syncLimitCheck.check(System.nanoTime())) {
            synchronized (leader) {
                id = leader.lastProposed;
            }
            QuorumPacket ping = new QuorumPacket(Leader.PING, id, null, null);
            queuePacket(ping);
        } else {
            LOG.warn("Closing connection to peer due to transaction timeout.");
            shutdown();
        }
    }

    /**
     * Queue leader packet of a given type
     *
     * @param type
     * @param zxid
     */
    private void queueOpPacket(int type, long zxid) {
        QuorumPacket packet = new QuorumPacket(type, zxid, null, null);
        queuePacket(packet);
    }

    void queuePacket(QuorumPacket p) {
        queuedPackets.add(p);
    }

    public boolean synced() {
        return isAlive()
                && leader.self.tick.get() <= tickOfNextAckDeadline;
    }

    /**
     * For testing, return packet queue
     *
     * @return
     */
    public Queue<QuorumPacket> getQueuedPackets() {
        return queuedPackets;
    }

    /**
     * For testing, we need to reset this value
     */
    public void setFirstPacket(boolean value) {
        needOpPacket = value;
    }
}
