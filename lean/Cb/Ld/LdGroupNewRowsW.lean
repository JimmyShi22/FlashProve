-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewRowsW.lean: this file is for toys (a toy: a small example instance): what is claimed
after the locations of a closing with standard new messages, as a family of linear claims on the
entries of the new messages, with forms and targets that are read off the public data; if the folded
complex has its laws.

In standard terms: after the verifier's queries in the code switch that follows the fold of several
oracle codewords, what remains to be proved of the new oracle codewords, beside what is carried, is,
if the folded complex has its laws (hC), a system of linear equations on their messages. Its
coefficients and right-hand sides are computed from x: the folded claim's explicit part, the old
samples, the locations and the symbols read there.

Definitions, statements as theorems, proofs. Generic: any carried joint, any riders.

Why: the stage after a closing claims, beside what is carried, `D.After x m`
(Cb/Req1/LdSegKit.lean): the folded claim on the cut, the old samples' answers on the slots, the
symbols read at the locations. The next segment has to take these claims along as rows.
Cb/Req1/LdSegAfterRows.lean has them as rows on all entries that are open;
Cb/Ld/LdGroupNewRideW.lean: their coefficients vanish off the new messages.

Main names:
  `V.aftF .. x j n`, `V.aftT .. x j`: the forms and the targets: for each name j : RowN of a claim:
    the coefficient at the entry n of a new message; the target.
  `stdNewW_after_all`: if the folded complex has its laws (hC), D.After x m ⇔ the rows on all
    entries hold (Cb/Req1/LdSegAfterRows.lean at the places of Cb/Ld/LdGroupNewRideW.lean).
  `stdNewW_after_new`: if the folded complex has its laws (hC), D.After x m ⇔ for every j: ∑ over
    the entries n of the new messages of aftF x j n · (the entry n of m) = aftT x j.
In all of them the group's set of common long positions, `G.P`, is nonempty (the closing needs it).

Limits: this file says nothing on any protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewRideW
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ)
  (Rd : RideD E ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp)) (Wp' : Type)
  (rst : Wp → Wp') (bkR : Rd.N.Msg → Wp' → Wp)

/-- an entry of a new message, after the locations -/
def StdNew.newAtW (n : V.N.N₀.Ent) : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Ent :=
  ⟨.inr (.inl n.1), n.2⟩

theorem stdNewW_newAt_inj : Function.Injective (V.newAtW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR) := by
  rintro ⟨a, j⟩ ⟨a', j'⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  obtain rfl : a = a' := Sum.inl.inj (Sum.inr.inj h1)
  exact congrArg (Sigma.mk a) (eq_of_heq h2)

/-- The forms and the targets. -/
def StdNew.aftF
    (x : ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Xc ×
        (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.hd.Smp) ×
      (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Lc)
    (j : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.RowN) (n : V.N.N₀.Ent) : E :=
  ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.rowsOf
      (V.pJW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR) (V.pQW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR)
      (Hd.foldD Sb sl Z A₀).slf id x).2
    j (V.newAtW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR n)
def StdNew.aftT
    (x : ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Xc ×
        (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.hd.Smp) ×
      (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Lc)
    (j : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.RowN) : E :=
  ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.rowsOf
    (V.pJW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR) (V.pQW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR)
    (Hd.foldD Sb sl Z A₀).slf id x).1 j

theorem stdNewW_after_all (hC : Sh.Cf.Laws)
    (x : ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Xc ×
        (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.hd.Smp) ×
      (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Lc)
    (m : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Msg) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.After x m ↔
    Slf.All (fun _ : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.RowN =>
        (Slf.idf : Slf E ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Ent → E)
          (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Ent))
      ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.rowsOf
        (V.pJW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR) (V.pQW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR)
        (Hd.foldD Sb sl Z A₀).slf id x)
      ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.ents m) :=
  ldLoc_after_rows E Kc _ _ _ _ _ _ (stdNewW_lin V Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR hC) x m

/-- What is claimed after the locations, as claims on the entries of the new messages.
(not all hypotheses are named here: see the statement below) -/
theorem stdNewW_after_new (hC : Sh.Cf.Laws)
    (x : ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Xc ×
        (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.hd.Smp) ×
      (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Lc)
    (m : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Msg) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.After x m ↔
    ∀ j, ∑ n : V.N.N₀.Ent, V.aftF Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR x j n *
        (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.ents
          m (V.newAtW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR n) =
      V.aftT Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR x j := by
  rw [stdNewW_after_all V Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR hC x m]
  refine forall_congr' fun j => ?_
  show (∑ n, _ * _ = _) ↔ _
  rw [← Fintype.sum_of_injective (V.newAtW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR)
      (stdNewW_newAt_inj V Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR)
      (fun n =>
        V.aftF Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR x j n *
          (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.ents
            m (V.newAtW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR n))
      _ (fun n hn => ?_) fun _ => rfl]
  · rfl
  · obtain ⟨o, e⟩ := n
    have h0 := stdNewW_rows_new V Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR x j ⟨o, e⟩ fun a ha => by
      obtain rfl : o = .inr (.inl a) := ha
      exact hn ⟨⟨a, e⟩, rfl⟩
    exact (congrArg
        (· * (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.ents m ⟨o, e⟩) h0).trans
      (zero_mul _)

end
end Cb
