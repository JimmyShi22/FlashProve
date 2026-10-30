-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/AtSel.lean: the code switch: the generator rows of the typed caller
switchSel, read at the entries of all open messages, in the form in which DrawJoin.lean's gen_join
meets them.

At the caller switchSel (Johnson/Top/H/SwitchSel.lean) what is claimed behind the positions is the
family of rows LdLocD.rowsOf (Cb/Req1/LdSegAfterRows.lean). Johnson/Top/H/SwitchRowsKept.lean has a
generator row's vector there in closed form (sel_gen) and its target (sel_target). An entry of the
open messages is an entry of a message that stayed open, or an entry of the new sending.
  sel_gen_new   at an entry of the new sending the vector is genVec (GenJoin.lean)
  sel_gen_old   at an entry of a message that stayed open it is 0
Both are one call of sel_gen and of pushTo_inr or pushTo_inl (Johnson/Top/H/SwitchMaps.lean).
LIMITS. Those of the files named: iJ and iQ are letters. No soundness is claimed.
-/
import Johnson.Top.H.SwitchRowsKept
import Johnson.Top.H0.K2Hands.DrawJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc
set_option quotPrecheck false in
local notation "pJK" => fun j : R.Sh.Cf.J =>
  ((⟨Sum.inr (iJ j).1, (iJ j).2⟩ : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Ent))
set_option quotPrecheck false in
local notation "pQK" => fun q : R.Sh.Cf.Q =>
  ((⟨Sum.inr (iQ q).1, (iQ q).2⟩ : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Ent))

/-- A generator row's vector at an entry of the new sending. -/
theorem sel_gen_new (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (iα : Fin (LocK).t × (LocK).C.Aa) (n : (sigOf cs l).Ent) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inr (.inr iα)) ⟨Sum.inr n.1, n.2⟩ =
      genVec R.s R.Kp iJ iQ (x.2.1 iα.1).val iα.2 n := by
  rw [sel_gen]
  exact congrArg₂ (· + ·)
    (pushTo_inr (A := (vecD (Hd.foldD Sb sl Z A₀)).S₂.O) (B := (sigOf cs l).O)
      (F := fun a => ((LocK).S.om a).C.J) iJ _ n)
    (pushTo_inr (A := (vecD (Hd.foldD Sb sl Z A₀)).S₂.O) (B := (sigOf cs l).O)
      (F := fun a => ((LocK).S.om a).C.J) iQ _ n)

/-- A generator row's vector at an entry of a message that stayed open. -/
theorem sel_gen_old (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (iα : Fin (LocK).t × (LocK).C.Aa) (a : (vecD (Hd.foldD Sb sl Z A₀)).S₂.O)
    (e : ((LocK).S.om (Sum.inl a)).C.J) :
    ((LocK).rowsOf pJK pQK Slf.idf id x).2 (.inr (.inr iα)) ⟨Sum.inl a, e⟩ = 0 := by
  rw [sel_gen]
  exact (congrArg₂ (· + ·)
    (pushTo_inl (A := (vecD (Hd.foldD Sb sl Z A₀)).S₂.O) (B := (sigOf cs l).O)
      (F := fun a => ((LocK).S.om a).C.J) iJ _ a e)
    (pushTo_inl (A := (vecD (Hd.foldD Sb sl Z A₀)).S₂.O) (B := (sigOf cs l).O)
      (F := fun a => ((LocK).S.om a).C.J) iQ _ a e)).trans (add_zero 0)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.sel_gen_new
#print axioms VerifiableInference.Desc.First.K2Hands.sel_gen_old
