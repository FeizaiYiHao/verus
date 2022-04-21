mod pervasive;

mod library {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::map::*,
    };

    #[spec]
    pub fn full_imap<K,V>(im:Map<K,V>) -> bool {
        forall(|k| im.dom().contains(k))
    }
}

// TODO(help): what's the equivalent of a module here?
mod host_identifiers {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::pervasive::*,
        crate::pervasive::set::*
    };

    fndecl!(pub fn num_hosts() -> int);

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    // TODO: Chris is suspicious that this argumentless-forall mightn't work
    pub fn axiom_num_hosts() {
        ensures(num_hosts() > 0);
    }

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item.
    // Sure would be nice to have it.
    //type HostId = int;
    #[derive(PartialEq, Eq, Structural)]
    pub struct HostId { pub value: int }

    #[spec]
    pub fn ValidHostId(h: HostId) -> bool {
        0 <= h.value && h.value < num_hosts()
    }

    #[spec]
    fn AllHosts() -> Set<HostId>
    {
        Set::new(|h: HostId| ValidHostId(h))
            //&& 0<=h.value<num_hosts()  // don't need Dafny's finite-set heuristic
    }
}

mod network {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
    };
    
    // NB jonh renamed to NetMessage to remedy ambiguity with protocol Message (payload).
    #[derive(PartialEq, Eq, Structural)]
    pub struct NetMessage<Payload> {
        pub sender: HostId,
        pub payload: Payload
    }

    // TODO(design): This is a lot of syntax for 'struct'; looking for brevity.
    //#[derive(PartialEq, Eq, Structural)]
    pub struct MessageOps<Payload>
    {
        pub recv:Option<NetMessage<Payload>>,
        pub send:Option<NetMessage<Payload>>,
        pub signed_msgs_to_check:Set<NetMessage<Payload>>
    }

    impl<Payload> MessageOps<Payload> {
        #[spec]
        pub fn is_send(self) -> bool {
               true
            && self.recv.is_None()
            && self.send.is_Some()
        }

        #[spec]
        pub fn no_send_recv(self) -> bool {
               true
            && self.recv.is_None()
            && self.send.is_None()
        }
    }

    //#[derive(PartialEq, Eq, Structural)]
    // Too bad, Set can't be Structural, so you'll have to .equal().
    pub struct Variables<Payload> {
        sent_msgs: Set<NetMessage<Payload>>
    }

    impl<Payload> Variables<Payload> {
        #[spec]
        pub fn init(v: Variables<Payload>) -> bool {
            equal(v.sent_msgs, set![])
        }

        #[spec]
        pub fn next(v: Variables<Payload>, vp: Variables<Payload>, msg_ops: MessageOps<Payload>, sender: HostId) -> bool {
               true
            // Only allow receipt of a message if we've seen it has been sent.
            && (msg_ops.recv.is_Some() >>= v.sent_msgs.contains(msg_ops.recv.value()))
            // Record the sent message, if there was one.
            && equal(vp.sent_msgs,
                    v.sent_msgs.union(
                        if msg_ops.send.is_Some() && msg_ops.send.value().sender == sender {
                            set![msg_ops.send.value()]
                        } else {
                            set![]
                        }))
            && msg_ops.signed_msgs_to_check.subset_of(v.sent_msgs)
        }
    }
}

mod messages {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::map::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::network::*,
    };

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type SequenceID = nat;
    #[derive(PartialEq, Eq, Structural)]
    pub struct SequenceID  { pub value: nat }

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type ViewNum = nat
    #[derive(PartialEq, Eq, Structural)]
    pub struct ViewNum  { pub value: nat }

    pub struct ClientOperation {
        pub sender: HostId,
        pub timestamp: nat
    }

    pub enum OperationWrapper {
        Noop,
        ClientOp { clientOperation: ClientOperation }
    }

    #[spec]
    pub fn senders_of(msgs: Set<NetMessage<Message>>) -> Set<HostId> {
        msgs.map(|msg: NetMessage<Message>| msg.sender)
    }

    #[spec]
    pub fn unique_senders(msgs: Set<NetMessage<Message>>) -> bool {
        forall(|m1, m2| #[auto_trigger]
                     true
                  && msgs.contains(m1)
                  && msgs.contains(m2)
                  && !equal(m1, m2)
              >>= m1.sender != m2.sender)
    }

    pub struct PreparedCertificate {
        pub votes: Set<NetMessage<Message>>
    }

    impl PreparedCertificate {
        #[spec]
        pub fn prototype(self) -> Message {
            recommends(self.votes.len() > 0);
            choose(|prot| self.votes.contains(prot)).payload
        }

        #[spec]
        pub fn wf(self) -> bool {
            forall(|v| #[auto_trigger] self.votes.contains(v) >>= v.payload.is_Prepare())
        }

        #[spec]
        pub fn empty(self) -> bool {
            self.votes.len() == 0
        }

        #[spec]
        pub fn valid(self, quorum_size: nat) -> bool {
               false
            || self.empty()
            || (   true
                && self.votes.len() == quorum_size
                && self.wf()
                // messages have to be votes that match eachother by the prototype 
                && forall(|v| #[auto_trigger] self.votes.contains(v) >>= equal(v.payload, self.prototype()))
                && unique_senders(self.votes)
                )
        }
    }

    pub struct ViewChangeMsgsSelectedByPrimary {
        msgs: Set<NetMessage<Message>>
    }

    impl ViewChangeMsgsSelectedByPrimary {
        #[spec]
        pub fn valid(self, view: ViewNum, quorum_size: nat) -> bool {
               true
            && self.msgs.len() > 0
            // All the ViewChange messages have to be for the same View. 
            && forall(|v| #[auto_trigger] self.msgs.contains(v) >>=
                         true
                      && v.payload.is_ViewChangeMsg()
                      && v.payload.wf()
                      && v.payload.get_new_view() == view
                      )
            && unique_senders(self.msgs)
            && self.msgs.len() == quorum_size
        }
    }

    #[is_variant]
    pub enum Message {
        PrePrepare { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        Prepare { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        Commit { view: ViewNum, seq_id:SequenceID, operation_wrapper: OperationWrapper },
        ClientRequest { client_op: ClientOperation },
        ViewChangeMsg { new_view: ViewNum, certificates: Map<SequenceID, PreparedCertificate> },
        NewViewMsg { new_view: ViewNum, vcMsgs: ViewChangeMsgsSelectedByPrimary },
    }

    impl Message {
        // TODO(utaal): Ewww
        #[spec] pub fn get_new_view(self) -> ViewNum {
            recommends(self.is_ViewChangeMsg() || self.is_NewViewMsg());
            match self {
                Message::ViewChangeMsg { new_view, .. } => new_view,
                Message::NewViewMsg { new_view, .. } => new_view,
                _ => arbitrary()
            }
        }
        // TODO(utaal,jonh) meh
        #[spec] pub fn get_view(self) -> ViewNum {
            recommends(self.is_PrePrepare() || self.is_Prepare() || self.is_Commit());
            match self {
                Message::PrePrepare { view, .. } => view,
                Message::Prepare { view, .. } => view,
                Message::Commit { view, .. } => view,
                _ => arbitrary(),
            }
        }
        #[spec]
        pub fn wf(self) -> bool {
            // TODO(jonh): Ewww
            // self.is_ViewChangeMsg() >>= full_imap(self.certificates())
            match self {
                Message::ViewChangeMsg { certificates, .. } => full_imap(certificates),
                _ => true,
            }
        }
    }
}

mod cluster_config {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
    };

    #[derive(PartialEq, Eq, Structural)]
    pub struct Constants {
        max_byzantine_faulty_replicas: nat,
        num_clients: nat
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.max_byzantine_faulty_replicas > 0 // Require non-trivial BFT system
            && self.num_clients > 0
        }

        #[spec]
        pub fn f(self) -> nat {
            recommends(self.wf());
            self.max_byzantine_faulty_replicas 
        }

        #[spec]
        pub fn n(self) -> nat {
            recommends(self.wf());
            3 * self.f() + 1
        }

        #[spec]
        pub fn cluster_size(self) -> nat {
            recommends(self.wf());
            self.n() + self.num_clients
        }

        #[spec]
        pub fn byzantine_safe_quorum(self) -> nat {
            recommends(self.wf());
            3 * self.f() + 1
        }

        #[spec]
        pub fn agreement_quorum(self) -> nat {
            recommends(self.wf());
            2 * self.f() + 1
        }

        #[spec]
        pub fn is_honest_replica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && self.f() <= id.value
            && id.value < self.n()
        }

        #[spec]
        pub fn is_faultyReplica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && 0 <= id.value
            && id.value < self.f()
        }

        #[spec]
        pub fn is_replica(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && 0 <= id.value
            && id.value < self.n()
        }

        #[spec]
        pub fn is_client(self, id: HostId) -> bool {
            recommends(self.wf());
               true
            && ValidHostId(id)
            && self.n() <= id.value
            && id.value < num_hosts()
        }
    }
}

mod client {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::host_identifiers::*,
        crate::messages::*,
    };

    #[derive(PartialEq, Eq, Structural)]
    pub struct Constants {
        my_id: HostId,
        cluster_config: cluster_config::Constants
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.cluster_config.wf()
            && self.cluster_config.is_client(self.my_id)    // NB: jonh upgraded to symbolic name
        }

        #[spec]
        pub fn configure(self, id: HostId, cluster_config: cluster_config::Constants) -> bool {
               true
            && self.my_id == id
            && self.cluster_config == cluster_config
        }
    }

    // Placeholder for possible client state
    #[derive(PartialEq, Eq, Structural)]
    pub struct Variables {
        last_request_timestamp: nat,
        last_reply_timestamp: nat
    }

    impl Variables {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && self.last_request_timestamp >= self.last_reply_timestamp
        }
    }
    
    #[spec]
    pub fn pending_requests(c: Constants, v: Variables) -> nat {
        recommends(v.wf(c));
        v.last_request_timestamp - v.last_reply_timestamp
    }

    #[spec]
    pub fn send_client_operation(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>) -> bool {
        let msg = msg_ops.send.value();
           true
        && v.wf(c)
        && msg_ops.is_send()
        && pending_requests(c, v) == 0
        && msg.payload.is_ClientRequest()
        && msg.sender == c.my_id
        && msg.payload.get_ClientRequest_client_op().sender == c.my_id
        && msg.payload.get_ClientRequest_client_op().timestamp == v.last_request_timestamp + 1
        && vp == Variables {
            last_request_timestamp: v.last_request_timestamp + 1,
            ..vp }
        // ...
    }
    
    #[spec]
    pub fn init(c: Constants, v: Variables) -> bool {
           true
        && v.wf(c)
        && v.last_request_timestamp == 0
        && v.last_reply_timestamp == 0
    }

    pub enum Step {
        SendClientOperationStep()
    }

    #[spec]
    pub fn next_step(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>, step: Step) -> bool {
        match step {
            Step::SendClientOperationStep() => send_client_operation(c, v, vp, msg_ops)
        }
    }

    #[spec]
    pub fn next(c: Constants, v: Variables, vp: Variables, msg_ops: network::MessageOps<Message>) -> bool {
        exists(|step| next_step(c, v, vp, msg_ops, step))
    }
}

mod replica {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::messages::*,
        crate::pervasive::map::*,
    };

    pub struct Constants {
        my_id: HostId,
        cluster_config: cluster_config::Constants
    }

    impl Constants {
        #[spec]
        pub fn wf(self) -> bool {
               true
            && self.cluster_config.wf()
            && self.cluster_config.is_replica(self.my_id)
        }

        #[spec] pub fn configure(self, id: HostId, cluster_conf: cluster_config::Constants) -> bool {
               true
            && self.my_id == id
            && self.cluster_config == cluster_conf
        }
    }

    // TODO(utaal): The verifier does not yet support the following Rust feature: unsupported item
    //type PrepareProofSet = Map<HostId, NetMessage<Message>>
    // TODO(utaal): Maps can't Structural, either.
    //#[derive(PartialEq, Eq, Structural)]
    struct PrepareProofSet {
        map: Map<HostId, network::NetMessage<Message>>
    }

    impl PrepareProofSet {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
            // TODO(utual): index(x) ==> [x]
            forall(|x| #[auto_trigger]
                   true
                && self.map.contains(x)
                && c.cluster_config.is_replica(self.map.index(x).sender))
        }
    }

    //type PrepareProofSet = Map<HostId, NetMessage<Message>>
    // TODO(utaal): Maps can't Structural, either.
    //#[derive(PartialEq, Eq, Structural)]
    struct CommitProofSet {
        map: Map<HostId, network::NetMessage<Message>>
    }

    impl CommitProofSet {
        #[spec]
        pub fn wf(self, c: Constants) -> bool {
            // TODO(utual): index(x) ==> [x]
            forall(|x| #[auto_trigger]
                   true
                && self.map.contains(x)
                && c.cluster_config.is_replica(self.map.index(x).sender))
        }
    }

    //type PrePreparesRecvd = Map<SequenceID, Option<network::NetMessage<Message>>>
    // TODO(utaal): Maps can't Structural, either.
    struct PrePreparesRcvd {
        map: Map<SequenceID, Option<network::NetMessage<Message>>>
    }

    impl PrePreparesRcvd {
        #[spec] pub fn wf(self) -> bool {
               true
            && full_imap(self.map)
            && forall(|x| #[auto_trigger]
                      self.map.contains(x) && self.map.index(x).is_Some()
                      >>= self.map.index(x).value().payload.is_PrePrepare())
        }
    }

    struct WorkingWindow {
        committed_client_operations: Map<SequenceID, Option<OperationWrapper>>,
        pre_prepares_rcvd: PrePreparesRcvd,
        prepares_rcvd: Map<SequenceID, PrepareProofSet>,
        commits_rcvd: Map<SequenceID, CommitProofSet>,
    }

    // TODO(chris): Discussion: I'm needing auto_trigger on EVERY forall. Is that expected?
    // Is it a sign that I'm an idiot? Will this be why this proof is so timeout-prone?
    impl WorkingWindow {
        #[spec] pub fn wf(self, c: Constants) -> bool {
               true
            && full_imap(self.committed_client_operations)
            && full_imap(self.prepares_rcvd)
            && full_imap(self.commits_rcvd)
            && self.pre_prepares_rcvd.wf()
            && forall(|seqID| #[auto_trigger] self.prepares_rcvd.contains(seqID) >>= self.prepares_rcvd.index(seqID).wf(c))
            && forall(|seqID| #[auto_trigger] self.commits_rcvd.contains(seqID) >>= self.commits_rcvd.index(seqID).wf(c))
        }
    }

    struct ViewChangeMsgs { msgs: Set<network::NetMessage<Message>> }
    impl ViewChangeMsgs {
        #[spec] fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && forall(|msg| #[auto_trigger] self.msgs.contains(msg) >>=
                     true
                  && msg.payload.is_ViewChangeMsg()
                  && c.cluster_config.is_replica(msg.sender))
        }
    }

    struct NewViewMsgs { msgs: Set<network::NetMessage<Message>> }
    impl NewViewMsgs {
        #[spec] fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && forall(|msg| #[auto_trigger] self.msgs.contains(msg) >>=
                     true
                  && msg.payload.is_NewViewMsg()
                  && c.cluster_config.is_replica(msg.sender))
        }
    }

    pub struct Variables {
        view: ViewNum,
        working_window: WorkingWindow,
        view_change_msgs_recvd: ViewChangeMsgs,
        new_view_msgs_recvd: NewViewMsgs,
    }
    impl Variables {
        #[spec] fn wf(self, c: Constants) -> bool {
               true
            && c.wf()
            && self.working_window.wf(c)
            && self.view_change_msgs_recvd.wf(c)
            && self.new_view_msgs_recvd.wf(c)
        }
    }

    #[spec] fn primary_for_view(c: Constants, view: ViewNum) -> nat {
        view.value % c.cluster_config.n()
    }

    #[spec] fn current_primary(c: Constants, v: Variables) -> nat {
        recommends(v.wf(c));
        primary_for_view(c, v.view)
    }

    // TODO(jonh): this was opaque in Dafny. Superstition?
    #[spec] fn have_sufficient_vc_msgs_to_move_to(c: Constants, v: Variables, new_view: ViewNum) -> bool {
        recommends(v.wf(c));
        let relevant_vc_msgs =
            Set::new(|vc_msg|
                   true
                && v.view_change_msgs_recvd.msgs.contains(vc_msg)
                && vc_msg.payload.get_new_view().value >= new_view.value);
        let senders = senders_of(relevant_vc_msgs);
        senders.len() >= c.cluster_config.byzantine_safe_quorum() //F+1
    }

    // TODO(jonh): this was opaque in Dafny. Superstition?
    #[spec] fn has_collected_proof_my_view_is_agreed(c: Constants, v: Variables) -> bool {
        let vc_msgs_for_my_view = Set::new(| msg|
                                           true
                                       && v.view_change_msgs_recvd.msgs.contains(msg)
                                       && msg.payload.get_new_view() == v.view
                                       );
        let senders = senders_of(vc_msgs_for_my_view);
           true
        && v.wf(c)
        && (
               false
            || v.view.value == 0 // View 0 is active initially therefore it is initially agreed.
            || senders.len() >= c.cluster_config.agreement_quorum()
           )
    }

    #[proof] fn set_reduction<E>(s: Set<E>, e: E)
    {
        requires(s.contains(e));
        ensures(s.difference(set![e]).len() < s.len());
    }

    // Constructively demonstrate that we can compute the certificate with the highest View.
    #[spec] fn highest_view_prepare_certificate(prepare_certificates: Set<PreparedCertificate>) -> PreparedCertificate {
        // TODO(chris): "only one call to recommends allowed"? Aw c'mooooon.
        recommends([
           forall(|cert| #[auto_trigger] prepare_certificates.contains(cert) >>= cert.wf() && !cert.empty()),
            prepare_certificates.len() > 0
        ]);
        // TODO(chris): "only one call to ensures allowed"? Aw c'mooooon.
        // TODO(jonh): guess this is a lemma
//        ensures(|out| [
//            prepare_certificates.contains(out),
//        // TODO(chris): Eeww. Having to type the out param is a bummer. Maybe macroland solves
//        // this?
//            forall(|other| prepare_certificates.contains(other) >>=
//                out.prototype().get_view().value >= other.prototype().get_view().value)
//        ]);
        decreases(prepare_certificates.len());

        let any = choose(|any| prepare_certificates.contains(any));
        if prepare_certificates.len() == 1 {
            // Nothing to prove in a fn; maybe needed in a lemma?
            // Library.SingletonSetAxiom(any, prepare_certificates);
            any
        } else {
            let rest = prepare_certificates.difference(set![any]);
            assert!(prepare_certificates.contains(any));
            set_reduction(prepare_certificates, any);
            assert!(rest.len() < prepare_certificates.len());
            let highest_of_rest = highest_view_prepare_certificate(rest);
            if any.prototype().get_view().value > highest_of_rest.prototype().get_view().value {
                any
            } else {
                highest_of_rest
            }
        }
    }
}

mod distributed_system {
    #[allow(unused_imports)]
    use {
        builtin::*,
        builtin_macros::*,
        crate::*,   // macros are defined at crate root somehow; need this for set![]
            // TODO(utaal): Need to put set! macro into module namespace for less confusion.
        crate::pervasive::*,
        crate::pervasive::set::*,
        crate::pervasive::option::*,
        crate::library::*,
        crate::host_identifiers::*,
        crate::messages::*,
    };

    pub enum HostConstants {
        Foo
//        Replica { replica_constants: Replica
//        max_byzantine_faulty_replicas: nat,
//        num_clients: nat
    }
}

fn main() {}