-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewRows.lean: for toys: take a closing with standard new messages. What is claimed
after its locations is a family of rows on the entries of the oracle messages that are left; this
holds whatever is carried, if the folded complex has its laws.

In the words of lean/GLOSSARY.md: toy: a small example instance. row: In `Cb/Ld/`, `Cb/Req1/`,
`Cb/Req2/` and `Cb/Part/`, a linear claim: a form on entries with a target, the value that the form
has to take (`Slf.Holds`, Cb/Ld/LdRel.lean).

Definitions, statements as theorems, proofs; `stdNew_lin`: by definition of the cut. No parameter of
a protocol. The generic form of `rqPJ`, `rqPQ`, `rq_lin` in Cb/Obj/LdObjectPartReq.lean.

Main names:
  `V.pJ`, `V.pQ`: where the entries of the folded complex (message, randomness) are among the
    entries of the oracle messages after the segment: in the new messages, at the places of
    Cb/Ld/LdGroupPlace.lean.
  `stdNew_lin`: the condition `Lin` of Cb/Req1/LdSegAfterRows.lean (the cut reads entries, at pJ and
    pQ; the claim Φ on the open word's message is a linear row; the open word's code has its laws)
    for `(V.close ..).loc`, from the laws of the folded complex; so `ldLoc_after_rows` applies: what
    is claimed after the locations holds if and only if all rows of `rowsOf` (targets and
    coefficient vectors) hold of the entries.
  `stdNew_rows_new`: these rows read the new messages alone: every coefficient at an entry of a
    message that crossed the closing (kept, not held) is 0.
In both theorems the group's set of common long positions, `G.P`, is nonempty (the closing needs
it).

Limits: what the head of Cb/Ld/LdGroupNewStd.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewStd
import Cb.Req1.LdSegAfterRows
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ)

def StdNew.pJ (j : Sh.Cf.J) : (V.close Sb sl Z A₀ w0 L t tl).loc.S.Ent :=
  ⟨.inr (V.N.place (.inl (.inl j))).1, (V.N.place (.inl (.inl j))).2⟩
def StdNew.pQ (q : Sh.Cf.Q) : (V.close Sb sl Z A₀ w0 L t tl).loc.S.Ent :=
  ⟨.inr (V.N.place (.inl (.inr q))).1, (V.N.place (.inl (.inr q))).2⟩

theorem stdNew_lin (hC : Sh.Cf.Laws) :
    (V.close Sb sl Z A₀ w0 L t tl).loc.Lin
      (V.pJ Sb sl Z A₀ w0 L t tl) (V.pQ Sb sl Z A₀ w0 L t tl) (Hd.foldD Sb sl Z A₀).slf id where
  cutJ := fun _ _ => rfl
  cutQ := fun _ _ => rfl
  form := fun _ _ => Iff.rfl
  laws := hC

/-- coefficients carried along p vanish off the image of p -/
theorem pushTo_off {E I J : Type} [AddCommMonoid E] [Fintype I] (p : I → J) (c : I → E)
    (n : J) (h : ∀ i, p i ≠ n) : pushTo p c n = 0 := by
  classical
  unfold pushTo
  exact Finset.sum_eq_zero fun i _ => if_neg (h i)

/-- For `G.P` nonempty: the rows read the new messages alone. -/
theorem stdNew_rows_new
    (x : ((V.close Sb sl Z A₀ w0 L t tl).loc.Xc × (V.close Sb sl Z A₀ w0 L t tl).loc.hd.Smp) ×
      (V.close Sb sl Z A₀ w0 L t tl).loc.Lc)
    (b : (V.close Sb sl Z A₀ w0 L t tl).loc.RowN) (a : (Hd.foldD Sb sl Z A₀).S₂.O)
    (j : ((Hd.foldD Sb sl Z A₀).S₂.om a).C.J) :
    ((V.close Sb sl Z A₀ w0 L t tl).loc.rowsOf
          (V.pJ Sb sl Z A₀ w0 L t tl) (V.pQ Sb sl Z A₀ w0 L t tl) (Hd.foldD Sb sl Z A₀).slf id x).2
        b ⟨.inl a, j⟩ = 0 := by
  have hJ : ∀ i, V.pJ Sb sl Z A₀ w0 L t tl i ≠ ⟨.inl a, j⟩ :=
    fun i h => by cases congrArg Sigma.fst h
  have hQ : ∀ i, V.pQ Sb sl Z A₀ w0 L t tl i ≠ ⟨.inl a, j⟩ :=
    fun i h => by cases congrArg Sigma.fst h
  rcases b with _ | ks | iα
  · exact pushTo_off _ _ _ hJ
  · exact pushTo_off _ _ _ fun i => hJ _
  · show pushTo _ _ _ + pushTo _ _ _ = 0
    rw [pushTo_off _ _ _ hJ, pushTo_off _ _ _ hQ, add_zero]

end
end Cb
