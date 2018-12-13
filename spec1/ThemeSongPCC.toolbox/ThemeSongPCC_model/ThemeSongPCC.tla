---------------------------- MODULE ThemeSongPCC ----------------------------

EXTENDS Integers

(*--fair algorithm ThemeSong {
    variables count = 5, s = "na";
      {
        while (count > 0) {
            either {
                s := "Batman";
                count := 0;
            } or {
                s := "na";
                count := count - 1;
            }
        };
        if (count = 0) {
            s := "Batman";
        }
      }
    } -*)
\* BEGIN TRANSLATION
VARIABLES count, s, pc

vars == << count, s, pc >>

Init == (* Global variables *)
        /\ count = 5
        /\ s = "na"
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF count > 0
               THEN /\ \/ /\ s' = "Batman"
                          /\ count' = 0
                       \/ /\ s' = "na"
                          /\ count' = count - 1
                    /\ pc' = "Lbl_1"
               ELSE /\ IF count = 0
                          THEN /\ s' = "Batman"
                          ELSE /\ TRUE
                               /\ s' = s
                    /\ pc' = "Done"
                    /\ count' = count

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

Batman == s = "Batman" /\ count = 0

Liveness == <>Batman
=============================================================================
\* Modification History
\* Last modified Sun Dec 09 17:11:39 GMT 2018 by ruben
\* Created Sun Dec 09 17:06:05 GMT 2018 by ruben
