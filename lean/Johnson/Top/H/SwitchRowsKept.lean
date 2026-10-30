-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchRowsKept.lean: the rows that a code switch behind the fold of a group with kept
main rows leaves open, each with its target and its vector of coefficients written out.

At the caller `switchSel` (Johnson/Top/H/SwitchSel.lean) what is claimed behind the positions is the
family of rows `LdLocD.rowsOf` (Cb/Req1/LdSegAfterRows.lean; `after_sel`). Here the group's shape is
`RowsK.Sh` (Johnson/Top/H/GroupRowsKept.lean), whose folded complex is `Sg.cKept`
(OnBytes/Slice/CsRowKept.lean). The three sorts of rows are unfolded; the generator's rows get the
closed form of `row_kept`. Statements and proofs; the first four hold by definition.
Main names (pJ, pQ: iJ and iQ as maps into the entries of all open messages):
  `cf_kept`: `R.Sh.Cf = R.s.cKept R.Kp`.
  `sel_claim`: the carried claim's row: the target and the vector of the statement, the vector
    carried along pJ (`pushTo`).
  `sel_sample`: a held member's old sample's row: the answer, and the sample's matrix at the seed,
    carried along pJ behind the member's slots.
  `sel_target`: a generator row's target is the long symbol's coordinate in the statement.
  `sel_gen`: a generator row's vector: `keptRow` at the drawn position, on the message's entries
    carried along pJ and on the tail's along pQ.
Limits: those of Johnson/Top/H/SwitchSel.lean: iJ and iQ are letters. Nothing says that a program's
rows are these.

-/
import Johnson.Top.H.SwitchSel
import Johnson.Top.H.GroupRowsKept
import OnBytes.Slice.CsRowKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

omit [Nonempty R.G.P] in
/-- The folded complex of a group with kept main rows. -/
theorem cf_kept : R.Sh.Cf = R.s.cKept R.Kp := rfl

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc
set_option quotPrecheck false in
local notation "pJK" => fun j : R.Sh.Cf.J =>
  ((⟨Sum.inr (iJ j).1, (iJ j).2⟩ : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Ent))
set_option quotPrecheck false in
local notation "pQK" => fun q : R.Sh.Cf.Q =>
  ((⟨Sum.inr (iQ q).1, (iQ q).2⟩ : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Ent))

/-- The carried claim's row. -/
theorem sel_claim (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).1 (.inl ()) = x.1.1.1 ∧
      ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inl ()) = pushTo pJK x.1.1.2 := ⟨rfl, rfl⟩

/-- A held member's old sample's row. -/
theorem sel_sample (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (ks : Σ k, ((LocK).hd.o k).Z.S) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).1 (.inr (.inl ks)) = (x.1.2 ks.1).2 ks.2 ∧
      ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inr (.inl ks)) =
        pushTo (fun j => pJK ((LocK).hd.sJ ks.1 j))
          (((LocK).hd.o ks.1).Z.mat (x.1.2 ks.1).1 ks.2) := ⟨rfl, rfl⟩

/-- A generator row's target. -/
theorem sel_target (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (iα : Fin (LocK).t × (LocK).C.Aa) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).1 (.inr (.inr iα)) = x.2.2 iα.1 iα.2 := rfl

/-- A generator row's vector, in closed form. -/
theorem sel_gen (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (iα : Fin (LocK).t × (LocK).C.Aa) (n : (LocK).S.Ent) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inr (.inr iα)) n =
      pushTo pJK (fun j => keptRow R.s R.Kp (x.2.1 iα.1).val iα.2 (.inl j)) n +
        pushTo pQK (fun q => keptRow R.s R.Kp (x.2.1 iα.1).val iα.2 (.inr q)) n := by
  exact congrArg₂ (· + ·)
    (congrArg (fun v => pushTo pJK v n) (funext fun j => row_kept R.s R.Kp _ iα.2 (.inl j)))
    (congrArg (fun v => pushTo pQK v n) (funext fun q => row_kept R.s R.Kp _ iα.2 (.inr q)))

end Johnson.Top.H

#print axioms Johnson.Top.H.cf_kept
#print axioms Johnson.Top.H.sel_claim
#print axioms Johnson.Top.H.sel_sample
#print axioms Johnson.Top.H.sel_gen
