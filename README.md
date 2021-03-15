# Formalizing E-222 using Lean

This repo is an attempt at working through the E-222 lectures, while generating TeX version of the notes and formalizing the work in Lean.

For any lecture or problem set, the goal is to formalize the notes and assumptions as close as possible to the flow of the material. For example,
we do not prove that `det(AB) = det(A)det(B)` when discussing invertible matrices, since the lecture does not. However, to showcase Lean, we might
define what a bijection is on our own instead of using the internal definition.

With cumulative lectures, the formalization of groups will build. If it is different that what Lean and mathlib rely on, those differences can
be highlighted, and later resolved or just contrasted.
