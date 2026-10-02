Dear Editors,

We are submitting our paper "Formalizing Flag Algebras in Lean" for consideration in the Annals of Formalized Mathematics.

The paper presents a Lean 4 formalization of Razborov's flag algebra method for finite simple graphs, covering flags and their densities, the flag algebra as a quotient vector space, positive homomorphisms, random extensions, and the downward operator. Building on this formalization, we develop a tactic that turns flag-algebra certificates found by semidefinite programming into Lean proofs. The tactic proves the up to thousands of finite density identities that a certificate relies on by verified computation, with adequacy theorems that connect each computation back to the abstract definitions, so that every computed fact is stated in the language of the formalized flag algebra. We also design a semantic interface for forbidden subgraphs that keeps the flag algebra independent of the forbidden family, so that a single development serves every problem. With this development we verify seven Turán-type upper bounds and the asymptotic forms of Mantel's theorem and the Erdős pentagon theorem. To our knowledge, the Erdős pentagon theorem has not previously been formalized in a proof assistant. The Lean development is open source and available at https://github.com/taeyool/lean-flag-algebras-release.

Thank you for considering our submission. If there are any questions or problems with our submission, please let us know.

Sincerely,
Gyeongwon Jeong, Seonghun Park, Jihoon Hyun, Sang-il Oum, and Hongseok Yang
