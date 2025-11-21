// Get Polylux from the official package repository
#import "@preview/polylux:0.4.0": *

// Make the paper dimensions fit for a presentation and the text larger
#set page(paper: "presentation-16-9")
#set text(size: 23pt, font: "Lato")

// Use #slide to create a slide and style it using your favourite Typst functions
#slide[
  #set align(horizon)

  = Extending the Group Theory Library in Mathlib
  =

  Lingyin Luo(洛聆尹)

  Dec.04.2025
]

#slide[
  == Motivation & Project Overview

  - Mathlib and its group theory library
    - using three theorems as stress-test to its current infrastructure
      - Abelian Simple Group
      - Hall Subgroup
      - Cauchy's theorem(the abelian group version)

  - Filling the possible gap and making PRs to Mathlib
  - Discussing the role of proof assist in math learning
]

#slide[
  == Proof strategy: using three theorems as show cases
  Forward reasoning: Abelian Simple Group
  ==
  - A clean argument where the structure flows from assumptions.
  - TODO
]

#slide[
  == Proof strategy: using three theorems as show cases
  Backward reasoning: Hall Subgroup
  ==
  - A problem where Lean formalization reveals structural fragility
  - TODO
]

#slide[
  == Proof strategy: using three theorems as show cases
  Induction: Cauchy's theorem(of abelian group)
  ==
  - A small but elegant induction example.
  - TODO

]

#slide[
  == Difficulty: The multi-layer nature in Fomalization
  ==
  e.g. Hall Subgroup in Math is a very clean statement.

  In Lean however, across at least 7 different layers: 
    - set and union of left cosets
    - group and subgroup
    - quotient group
    - cardinality, index and corresponding ambient type
    - lattice operation
    - homomorphism and isomorphism
    - coprime property
]

#slide[
  == Current state and possible improvements
  ===
  - TODO
 
]

#slide[
  == Reflection: role of a proof assist in math learning
  == 
  - Pro: Formalization reveals structure that is invisible on paper
    - eg: TODO
  - Con: Sometimes might let the technical details bury the intuition
    - eg: TODO
]

#slide[
  == Q&A
  ===
  - Any questions or suggestions :)?
 
]
