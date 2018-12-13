## Formally Verifying __Complex Systems__ Using $$TLA^+$$

---

---

![](Images/RubenBerenguel.jpg)
![](Images/scala.png)
![](Images/python.png)

# whoami

- Ruben Berenguel (@berenguel)
- PhD in Mathematics
- (big) data consultant
- Senior big data engineer using **Python**, **Go** and **Scala**

---

# [fit] Formal methods
# [fit] __Why?__

---

![](images/Example1.png)

^ I had a system based in Akka

---

![](images/Example2.png)

^ Requiring to communicate with many external systems (via TCP)

---

![](images/Example3.png)

^ The system was using Akka persistence to store its internal state mutations

---

![](images/Example4.png)

^ An external "source" (say, a user) would trigger a change request that would need to be forwarded to the external systems when they were available. The state of the request goes into the internal state of the actor.

---

![](images/Example5.png)

^ And they should answer fulfilment status of the request when possible. How can I be sure the external services get the request, and the actor system get the confirmation, given the large amount of possible states that persistence introduces?

---

# 💡...

---

![right](images/bat_zoom.png)

# What are _formal methods_?

[.build-lists: true]

- __Technique__ for specifying the behaviour of hardware or software
- Based on some __mathematical formalism__ or __theory__

---

# Examples

[.build-lists: true]

- Lambda calculus
- (possibly dependent) Type systems
- TLA (_T_emporal _L_ogic of _A_ctions)

---

[.build-lists: true]

## What does formal verification require?

- Write a __specification__ of what the system is supposed to do
- Computationally verify the __desired properties__
- Optionally/Additionally: __Prove__ the desired properties of the system

^A specification is an abstraction: it describes some aspects of the system and
ignores others. We want the specification to be as simple as possible (but, like
someone famous said, _not simpler_)

---

[.build-lists: true]

## What is $$TLA^+$$?

---

### Formal specification language developed on top of __TLA__ by Leslie Lamport[^1]

#### Models written in $$TLA^+$$ can be checked using __TLC__

[^1]: The _La_ from $$\LaTeX$$ and the, well, author of the [Paxos](https://en.wikipedia.org/wiki/Paxos_(computer_science)) consensus algorithm, among many other things

^ _Temporal Logic_ was introduced in the late 1950s, and LLs Temporal Logic of Actions was published in 1994. The $$TLA^+$$ language was introduced in 1999, late that year TLC was started

--- 

### A pseudocode-like language, __PlusCal__ transpiles into $$TLA^+$$, and can be used for sequential algorithms
 
#### Comes in two flavours, __P__[^2] and __C__[^3]

[^2]: P of _Pascal_? `begin while do stuff end while;`

[^3]: C as in _C_, {curly curly}

^ PlusCal (formerly +Cal) has been available since 2009

---

### An additional proof system __TLAPS__[^4] can be used to check proofs

#### This is how __Bizantyne Paxos__[^5] was proven, and has been used in several industry projects

[^4]: Can be found [here](http://tla.msr-inria.inria.fr/tlaps/content/Home.html), it's separate from the TLA+ Toolbox

[^5]: [Mechanically Checked Safety Proof of a Byzantine Paxos Algorithm](http://lamport.azurewebsites.net/tla/byzpaxos.html)

^ Has been used for proving soundness in Azure's CosmosDB, for instance

---

 __System__ | __Components__ | __Lines of Code__ | __Result__
------ | ---------- | :---: | ------
_S3_ | _Fault tolerant network algo_ | _804 (PlusCal)_ | _2 bugs, further bugs in later optimisations_
S3 | Background redistribution | 645 (PlusCal) | 1 bug, 1 bug in the fix
_DynamoDB_ | _Replication & membership_ | _939 (PlusCal)_ | _3 bugs (35 step trace)_
EBS | Volume management | 223 (PlusCal) | Better confidence
_Internal lock manager_ | _Replication_ | _318 TLA+_ | _1 bug_

^ Here we can see some examples of use from Amazon Web Services (from [here](http://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf))

---

## How does $$TLA^+$$ look like?

^ I will show a simple infinite state machine in TLA+

---

![right](images/nanana.mp4)

```
-- MODULE ThemeSong --

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
```

---

![right](images/empty.png)

```
-- MODULE ThemeSong --

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
```

---

![right](images/empty.png)

[.code-highlight: 17]

```
-- MODULE ThemeSong --

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
```

^ This is the specification of the system

---


![right](images/Na_.png)

[.code-highlight: 9]

```
-- MODULE ThemeSong --

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
```

^ And this is the initial state

---

![right](images/NaNa_.png)

[.code-highlight: 11-15]

```
-- MODULE ThemeSong --

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
```

^ The next state after is an "either" state when `count > 0`

---

![right](images/NaNaNa_.png)

[.code-highlight: 12]

```
-- MODULE ThemeSong --

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
```

^ When this branch is considered, all future states are the same

---

![right](images/NaNaNaNa_.png)

[.code-highlight: 11]

```
-- MODULE ThemeSong --

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
```

^ The other branch decreases the counter, and then we can repeat

---

![right](images/NaNaNaNaNa_.png)


[.code-highlight: 9-15]

```
-- MODULE ThemeSong --

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
```

---

![right](images/NaNaNaNaNaBatman_.png)

[.code-highlight: 21]

```
-- MODULE ThemeSong --

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
```

^ And this is a condition we can request TLC to verify: eventually the state of the system has "Batman" and 0

---

## How would the equivalent __PlusCal__ algorithm look like?

![right](images/Batusi.gif)

---

![right](images/robin.jpg)

[.code-highlight: all]
[.code-highlight: 1]
[.code-highlight: 5]
[.code-highlight: all]


```
(*--fair algorithm ThemeSong {
    variables count = 2, s = "na";
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
```

^ Next slide will contain horrible autogenerated code

---

![right](images/bat_pouting.jpg)

```
VARIABLES count, s, pc

vars == << count, s, pc >>

Init == /\ count = 2
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
           \/ (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)
```

---

### We can "easily" model whole systems using __PlusCal__ 
#### Like…

---

```scala
case class Trigger(payload: Payload)

class SimpleActor extends Actor {
  def receive = {
    case Trigger(payload) => ThirdParty().trigger(payload)
    case _                => log.warn("Duh")
  }
}
```

^Here we have a very, very simple actor that on receiving a `Trigger` message, will ping a third party with the paylod.

---

### With __PlusCal__ we can model concurrent (or not) systems by using `process`

^ Although $$TLA^+$$ can express more models than PlusCal can, it's way easier to define sequential processes running possibly in parallel in PlusCal

---

```
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
```

^ This is how an actor system roughly equivalent to the previous actor would look like. I'll break it up in the next slides

---

[.code-highlight: all]
[.code-highlight: 1-2]

```
variables actorInboxes = [ actor |-> <<>> ];
          triggered = FALSE;

procedure trigger(trigger_content="?") {
    triggerLabel:
      triggered := TRUE;
      return;
}
```

^ This just sets up some inbox system, ignores the fact that the third party provider may fail receiving the request and sets the scene for checking some property

---

[.code-highlight: all]
[.code-highlight: 1]
[.code-highlight: 10-15]
[.code-highlight: 16-19]
[.code-highlight: all]

```
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
```

^ This is a possible approach of what the actor might look like. It starts by seeding the inbox with a trigger (you can alternatively add a different process to do so, but this is better when you don't care about the source). Then it calls the trigger process if it _receive_s a trigger message

---

A possible check on this system could then be

```
Triggered == triggered = TRUE

Liveness == <>Triggered
```

^ We could for instance check that eventually the third party system is triggered. This is what I did in my problem in the beginning: Do the action happen on the remote server, and the confirmation eventually makes it into the actor system? In a space of around 14 thousand states, the answer was yes.

---

![](images/BatmanWest-crop.jpg)

# [fit] __QUESTIONS?__

---

![110%](images/thanks.png)

---

# Further references

[Downloading the TLA Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html)

[Specifying systems by Leslie Lamport](https://lamport.azurewebsites.net/tla/book.html)[^SSLL]

[Practical TLA+ by Hillel Wayne](https://www.apress.com/gb/book/9781484238288)[^PTHW]

[^SSLL]: This is the main reference for TLA+, and although it can look a bit dense it reads very well.

[^PTHW]: This is a lighther first reference, focused in PlusCal (using the __P__ syntax). I started with this book, and with it you can easily get enough PlusCal to define your specifications and validate your models

---

[TLA+ Video Course by Leslie Lamport](https://lamport.azurewebsites.net/video/videos.html)[^TVC]

[Learn TLA online book by Hillel Wayne](https://learntla.com/introduction/)[^LTHW]


[^TVC]: This is a video course by Lamport, total of around 4 hours

[^LTHW]: An online book by Hillel Wayne covering parts of _Practical TLA+_

---

# EOF
