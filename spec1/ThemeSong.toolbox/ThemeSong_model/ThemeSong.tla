------------------------------- MODULE ThemeSong -------------------------------

EXTENDS Integers

VARIABLES s, count

vars == <<s, count>>

Sinit == s = "na" /\ count = 2

Na == s' = "na" /\ count' = count - 1
ToB == s' = "Batman" /\ count' = 0

Snext == IF count > 0 THEN /\ ( Na \/ ToB)
                      ELSE /\ ToB

Spec == Sinit /\ [][Snext]_vars /\ WF_vars(ToB)

Batman == s = "Batman" /\ count = 0

Liveness == <>Batman

=============================================================================
\* Modification History
\* Last modified Tue Dec 11 08:51:52 GMT 2018 by ruben
\* Created Sun Dec 09 12:06:22 GMT 2018 by ruben
