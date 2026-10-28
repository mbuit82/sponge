# Derived Rules

Here are a list of derived rules currently supported by sponge. They are currently across files in the [`DerivedRules`](DerivedRules) directory. Reading the code for these is a bit opaque I think, but once you get the hang of it I think it is definitely possible to define your own derived rules. 

## Applying theorems/proofs
Given we are working in an axiomatic system, it would be awfully nice to have derived rules of the shape for, e.g. conjunction introduction `A -> B -> (A & B)`, 
```
A   B
------
(A & B)
```
Fortunately you don't need to write a derived rule for that—sponge does it automatically! 
Particularly, the line `n |- (A & B)   by And Intro: i j` tells sponge to make an instance of axiom `And Intro`, and then apply the contents of lines `i` and `j` to that axiom with modus ponens (so lines `i` and `j` should have `A` and `B`, respectively). 

You can do this with theorems, too. A particularly common example of this with theorems is hypothetical syllogism, `|- (P -> Q) -> (Q -> R) -> (P -> R)`. Given a line `i` with content `P -> Q` and `j` with content `Q ->R`, by having the justification `by applying hypothetical_syllogism (from minimal): i j` on a line with content `P -> R`. (The way this is done is optimized for proofs that use deduction in order to avoid unfolding deduction. See "Simulating cut on proofs using the deduction theorem" under Optimizations in [`ARCHITECTURE.md`](ARCHITECTURE.md).)


## Derived rules supported
The names are kind of arbitrary and just reflect how I think of them. Please do let me know if there are more accepted names. 

Deduction:
```
P |- Q
--------
|- P -> Q
```
Strengthening:
```
|- X -> Y
-----------
|- (P -> ... -> X) -> (P -> ... -> Y)
```
Weakening: 
```
|- X -> Y
-----------
|- (P -> ... -> Y -> Q) -> (P -> ... -> X -> Q)
```
Embedding: 
```
|- P -> Q -> ... -> R
-----------------------
|- (X -> P) -> (X -> Q) -> ... -> (X -> R)
```
For strengthening and weakening, you can supply another line number to your justification to get the following derived rules:
```
|- X -> Y     (P -> ... -> X)
-------------------------------
|- (P -> ... -> Y)
```
```
|- X -> Y     (P -> ... -> Y -> Q)
-----------------------------------
|- (P -> ... -> X -> Q)
```
See [the proof of `ML`'s normality in S4.2](user_proofs/S4.2/diamond_box_normal.txt) for an example of this usage. 


### K reasoning
K reasoning does one of the following three derived rule, depending on the content of the current line and the cited line:
```
|- P -> Q -> ... -> R
------------------------
|- LP -> LQ -> ... LR
```
```
|- L(P -> Q -> ... -> R)
-------------------------
|- LP -> LQ -> ... LR
```
```
|- P -> Q
------------
|- MP -> MQ
```
Note that the first and second derived rules can stop at any arbitrary point in the chain `P -> Q -> ... -> R`. 