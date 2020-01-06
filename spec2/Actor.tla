------------------------------- MODULE Actor -------------------------------

EXTENDS TLC, Integers, Sequences

(*--fair algorithm ActorStuff {

variables actorInboxes = [ actor |-> <<>> ];
          triggered = FALSE;

procedure trigger(trigger_content="?") {
    triggerLabel:
      triggered := TRUE;
      return;
}

fair process (actor = "actor")
variables currentMessage = <<"?", "no_content">>;
  kind = "?";
  content = "no_content";
{
  Send:
    actorInboxes["actor"] := Append(actorInboxes["actor"], <<"trigger", "foo">>);
  WaitForMessages:+
    while (TRUE) {
      if (actorInboxes["actor"] /= <<>>) {
         currentMessage := Head(actorInboxes["actor"]);               
         content := Head(Tail(currentMessage));
         kind := Head(currentMessage);
         actorInboxes["actor"] := Tail(actorInboxes["actor"]);
        };
        ProcessMessage:
         if (kind = "trigger") {
           call trigger(content);
         }
    }
}

}
*)
\* BEGIN TRANSLATION
VARIABLES actorInboxes, triggered, pc, stack, trigger_content, currentMessage, 
          kind, content

vars == << actorInboxes, triggered, pc, stack, trigger_content, 
           currentMessage, kind, content >>

ProcSet == {"actor"}

Init == (* Global variables *)
        /\ actorInboxes = [ actor |-> <<>> ]
        /\ triggered = FALSE
        (* Procedure trigger *)
        /\ trigger_content = [ self \in ProcSet |-> "?"]
        (* Process actor *)
        /\ currentMessage = <<"?", "no_content">>
        /\ kind = "?"
        /\ content = "no_content"
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Send"]

triggerLabel(self) == /\ pc[self] = "triggerLabel"
                      /\ triggered' = TRUE
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ trigger_content' = [trigger_content EXCEPT ![self] = Head(stack[self]).trigger_content]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << actorInboxes, currentMessage, kind, 
                                      content >>

trigger(self) == triggerLabel(self)

Send == /\ pc["actor"] = "Send"
        /\ actorInboxes' = [actorInboxes EXCEPT !["actor"] = Append(actorInboxes["actor"], <<"trigger", "foo">>)]
        /\ pc' = [pc EXCEPT !["actor"] = "WaitForMessages"]
        /\ UNCHANGED << triggered, stack, trigger_content, currentMessage, 
                        kind, content >>

WaitForMessages == /\ pc["actor"] = "WaitForMessages"
                   /\ IF actorInboxes["actor"] /= <<>>
                         THEN /\ currentMessage' = Head(actorInboxes["actor"])
                              /\ content' = Head(Tail(currentMessage'))
                              /\ kind' = Head(currentMessage')
                              /\ actorInboxes' = [actorInboxes EXCEPT !["actor"] = Tail(actorInboxes["actor"])]
                         ELSE /\ TRUE
                              /\ UNCHANGED << actorInboxes, currentMessage, 
                                              kind, content >>
                   /\ pc' = [pc EXCEPT !["actor"] = "ProcessMessage"]
                   /\ UNCHANGED << triggered, stack, trigger_content >>

ProcessMessage == /\ pc["actor"] = "ProcessMessage"
                  /\ IF kind = "trigger"
                        THEN /\ /\ stack' = [stack EXCEPT !["actor"] = << [ procedure |->  "trigger",
                                                                            pc        |->  "WaitForMessages",
                                                                            trigger_content |->  trigger_content["actor"] ] >>
                                                                        \o stack["actor"]]
                                /\ trigger_content' = [trigger_content EXCEPT !["actor"] = content]
                             /\ pc' = [pc EXCEPT !["actor"] = "triggerLabel"]
                        ELSE /\ pc' = [pc EXCEPT !["actor"] = "WaitForMessages"]
                             /\ UNCHANGED << stack, trigger_content >>
                  /\ UNCHANGED << actorInboxes, triggered, currentMessage, 
                                  kind, content >>

actor == Send \/ WaitForMessages \/ ProcessMessage

Next == actor
           \/ (\E self \in ProcSet: trigger(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(actor) /\ SF_vars(WaitForMessages) /\ WF_vars(trigger("actor"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Triggered == triggered = TRUE

Liveness == <>Triggered

=============================================================================
\* Modification History
\* Last modified Sun Jan 20 22:55:17 GMT 2019 by ruben
\* Created Sun Dec 09 19:56:50 GMT 2018 by ruben
