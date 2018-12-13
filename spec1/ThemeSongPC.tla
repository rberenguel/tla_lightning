---------------------------- MODULE ThemeSongPC ----------------------------

EXTENDS Integers

(*--fair algorithm ThemeSong
    variables count = 5, s = "na"
    begin ThemeSong:
        while count > 0 do
            either
                s := "Batman";
                count := 0;
            or
                s := "na";
                count := count - 1;
            end either;
        end while;
        if count = 0 then
            s := "Batman";
        end if;
    end algorithm; -*)

\* BEGIN TRANSLATION
VARIABLES count, s, pc

vars == << count, s, pc >>

Init == (* Global variables *)
        /\ count = 5
        /\ s = "na"
        /\ pc = "ThemeSong"

ThemeSong == /\ pc = "ThemeSong"
             /\ IF count > 0
                   THEN /\ \/ /\ s' = "Batman"
                              /\ count' = 0
                           \/ /\ s' = "na"
                              /\ count' = count - 1
                        /\ pc' = "ThemeSong"
                   ELSE /\ IF count = 0
                              THEN /\ s' = "Batman"
                              ELSE /\ TRUE
                                   /\ s' = s
                        /\ pc' = "Done"
                        /\ count' = count

Next == ThemeSong
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
\* Last modified Sun Dec 09 16:46:14 GMT 2018 by ruben
\* Created Sun Dec 09 16:24:08 GMT 2018 by ruben
