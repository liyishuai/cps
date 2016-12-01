# cps
Conversion from System T to continuation-passing style (CPS)

## System K
System K is an extension of System T, with the following features:

* `void` type
* `let x = d in e` and `halt e` terms

I am working on a simplified version without recursions.  
You can see the definitions in [k.pdf](k.pdf).

## Continuations
Programs in System K are terms of type `void`.  
Continuations are lambda expressions that
takes a term and returns a program i.e.

    Gamma |- u : t
    --------------------
    Gamma |- k(u) : void

An example of continuation is `\u:t. halt u^t`,
in which `u^t` is a term with its type annotated.

## Conversion: T to K
### Type conversion
|     t    |           K[[t]]           |
|:--------:|:--------------------------:|
|    int   |             int            |
| t1 -> t2 | K[[t1]]->Kcont[[t2]]->void |
in which `Kcont[[t]] = K[[t]] -> void`

### Program conversion
`Kprog[[u^t]] = Kexp[[u^t]](\x:K[[t]]. halt x^K[[t]])^Kcont[[t]]`  
in which `Kexp` conversion is defined as follows:

`Kexp[[e]] : Kcont[[t]] -> void` in which `e` has type `t`

| e | Kexp[[e]] k |
|:---:|:-----------:|
| y^t | k(y^K[[t]]) |
| \x:t1. e^t2 | k(\x:K[[t1]]. \c:Kcont[[t2]]. Kexp[[e]] c^Kcont[[t2]])^K[[t1->t2]] |
| u1^t1 u2^t2 | Kexp[[u1^t1]] \x1:K[[t1]]. Kexp[[u2^t2]] \x2:K[[t2]]. x1^K[[t1]] x2^K[[t2]] k^Kcont[[t2]]^Kcont[[t1]] |
| (e1 p e2)^t | Kexp[[e1]] \x1:int. Kexp[[e2]] \x2:int. let y = x1 p x2 in k(y^int)^Kcont[[int]]^Kcont[[int]] |
| if0(e1, e2, e3)^t | Kexp[[e1]] \x:int. if0(x^int, Kexp[[e2]] k, Kexp[[e3]] k)^Kcont[[int]] |

### Type correctness
    forall e t, |- e : t -> |- Kprog[[e]] : void

## Roadmap
- [x] Formalize System T and System K
- [ ] Implement conversion from T to K
- [ ] Prove type correctness
