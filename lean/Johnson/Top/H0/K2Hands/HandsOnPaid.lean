-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/HandsOnPaid.lean: the code switch: THE LAST JOIN (HandsOn.lean), AT
THE PROGRAM's OWN FRAME: HandsOn.lean's hands_on_rows at the two maps of names that are written out
of the program's frame, with four of its records of premises (FrameOK, Names, NamesK, ClaimOK)
replaced by the one record AtSwitch on the program's own frame and test (Paid.lean) and four plain
clauses on the old claim and the frame.
  hands_on_paid   for every typed row b: the row at rows[rowNo … b]? has b's target and vector, and
                  no coefficient elsewhere
WHAT IS STILL PREMISE: that switchRows has laid the rows (Laid: RowsAt.lean's laid_of gives it from
the maker's yes); AtSwitch; the main form's tensors have the main code's index bits; the two
written-out vectors are no longer than the mask code's message; two kept members have two old
numbers; and TieN, on the typed statement, handed in whole: with its named premise on the typed
sample's matrix, AND WITH THE CLAUSE «Slots …» INSIDE ITS «sample», which stays a premise
(Paid.lean's paid_slots would give it from AtSwitch and W.kept[aOf ks.1]? = some k; it is called by
paid_claim alone). Nothing here shows that a run of the programs meets them. (Brought further, not
paid: AtYes.lean; TiePaid.lean.) No new reasoning. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.HandsOn
import Johnson.Top.H0.K2Hands.Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)
  {St : OnBytes.Statement} {old : OnBytes.SingleRows} {T : OnBytes.SwitchTarget} {g : ℕ}
  {anew : Array ℕ} {W : OnBytes.SwitchFrame} {ids : ℕ → ℕ} {l : List (OnBytes.OracleShape × ℕ)}
  {mem row : R.Kp → ℕ} {pl : R.Kp → OnBytes.KeptPlace}
  (A : AtSwitch St old T g anew W l R.s R.Kp mem row pl ids)

set_option quotPrecheck false in
local notation "LocA" => (closeSel Hd Sb sl Z A₀ St.codes l A.mapJ A.mapQ t w₀).loc

/-- **The last join, row by row, at the frame's own maps of names.** -/
theorem hands_on_paid {pos : OnBytes.Positions} {y : Array OnBytes.E} {rows : List OnBytes.Row}
    {carried : OnBytes.Row} (L : Laid St old T g anew pos y rows W carried)
    (mainVars : ∀ v ∈ old.c.tensors, v.vars = W.code.logEll)
    (d0 : (old.d.getD 0 #[]).size ≤ W.zk.ell) (d1 : (old.d.getD 1 #[]).size ≤ W.zk.ell)
    (twoOld : ∀ (a a' : ℕ) (k k' : OnBytes.KeptPlace), W.kept[a]? = some k → W.kept[a']? = some k' →
      k.old = k'.old → a = a')
    {aOf : (LocA).hd.K → ℕ}
    {iOf : ∀ k, ((LocA).hd.o k).Z.S → ℕ}
    (x : ((LocA).Xc ×
      (LocA).hd.Smp) ×
      (LocA).Lc)
    (X : TieN R Hd Sb sl Z A₀ St.codes l A.mapJ A.mapQ t w₀ x St W ids old pos y mem row pl aOf iOf)
    (b : (LocA).RowN) :
    ∃ r : OnBytes.Row, rows[rowNo R.s R.Kp St W mem row aOf iOf b]? = some r ∧
      readE r.target = ((LocA).rowsOf
        (fun j : R.Sh.Cf.J => (⟨Sum.inr (A.mapJ j).1, (A.mapJ j).2⟩ : (LocA).S.Ent))
        (fun q : R.Sh.Cf.Q => (⟨Sum.inr (A.mapQ q).1, (A.mapQ q).2⟩ : (LocA).S.Ent))
        Slf.idf id x).1 b ∧
      (∀ n : (sigOf St.codes l).Ent,
        coefAt r (ids (entAt St.codes l n).1) (entAt St.codes l n).2.1 (entAt St.codes l n).2.2 =
          ((LocA).rowsOf
            (fun j : R.Sh.Cf.J => (⟨Sum.inr (A.mapJ j).1, (A.mapJ j).2⟩ : (LocA).S.Ent))
            (fun q : R.Sh.Cf.Q => (⟨Sum.inr (A.mapQ q).1, (A.mapQ q).2⟩ : (LocA).S.Ent))
            Slf.idf id x).2 b ⟨Sum.inr n.1, n.2⟩) ∧
      (∀ (a : (vecD (Hd.foldD Sb sl Z A₀)).S₂.O) (e : ((LocA).S.om (Sum.inl a)).C.J),
        ((LocA).rowsOf
          (fun j : R.Sh.Cf.J => (⟨Sum.inr (A.mapJ j).1, (A.mapJ j).2⟩ : (LocA).S.Ent))
          (fun q : R.Sh.Cf.Q => (⟨Sum.inr (A.mapQ q).1, (A.mapQ q).2⟩ : (LocA).S.Ent))
          Slf.idf id x).2 b ⟨Sum.inl a, e⟩ = 0) ∧
      OnlyAt St.codes l ids (Inside R.s W pl) r :=
  hands_on_rows R Hd Sb sl Z A₀ St.codes l A.mapJ A.mapQ t w₀ L (paid_frame A) (paid_names A)
    (paid_namesK A) A.slots.member A.slots.rowIn (check_facts A.check).1 rfl rfl
    (fun ks hks => paid_claim A mainVars d0 d1 twoOld ks hks) x X b

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.hands_on_paid
