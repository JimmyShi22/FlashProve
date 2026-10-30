-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/AfterText.lean: the code switch: IF EVERY ROW THAT THE PROGRAM LAYS
HOLDS OF THE NEW MESSAGES, THE TYPED CLAIM BEHIND THE POSITIONS (LdLocD.After) HOLDS; and back.

HandsOn.lean's hands_on_rows compares the typed rows of the caller switchSel with the rows of the
program's list, coefficient by coefficient. The library says what the typed rows are for:
ldLoc_after_rows (Cb/Req1/LdSegAfterRows.lean): under LdLocD.Lin, After x u holds just if all rows
of rowsOf hold of u's entries. Here the two are joined, so that the text's side of the tie of the
switch's law over written rounds (the premise hT of sel_law, Johnson/Top/H/SwitchLeads.lean) is a
sentence on the program's own list of rows.
  TextHolds     A ROW OF THE TEXT HOLDS of a vector v on the entries of the new sending: the sum
                over these entries of the row's coefficient at the entry's three numbers, times v at
                the entry, is the row's target, read in the field. THE MEANING IS SAID ON ENTRIES:
                an index of a table that names no entry has no share.
  newEnt, newEnt_inj  an entry of the new sending among all entries behind the switch; the map is
                one to one
  sum_new       a sum over all entries of the open and the new messages, of a function that is 0 at
                the open ones
  typed_iff     for one typed row b and the program's row r at its place: b holds of u just if r
                holds of u's new messages
  after_of_text  all rows of the list hold ⇒ After x u
  text_of_after  After x u ⇒ all rows of the list hold (with the numbering onto: SlotsAll, Held, as
                many draws as typed positions)
LIMITS. All premises of hands_on_rows stay premises, and LdLocD.Lin is one more (lin_loc,
Johnson/Top/H/AfterLay.lean, gives the like at «Dd.slf id» from the cut's two laws and the folded
complex's; that this is the «Slf.idf id» asked here is not shown in this file). No soundness is
claimed.
-/
import Johnson.Top.H0.K2Hands.HandsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

/-- **A row of the text holds** of a vector on the entries of the new sending. -/
def TextHolds (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (ids : ℕ → ℕ)
    (r : OnBytes.Row) (v : (sigOf cs l).Ent → GE) : Prop :=
  ∑ n : (sigOf cs l).Ent,
    coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 * v n = readE r.target

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
set_option quotPrecheck false in
local notation "OldO" => (vecD (Hd.foldD Sb sl Z A₀)).S₂.O

/-- An entry of the new sending, among all entries behind the switch. -/
def newEnt (n : (sigOf cs l).Ent) : (LocK).S.Ent := ⟨Sum.inr n.1, n.2⟩

theorem newEnt_inj : Function.Injective (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  cases h
  rfl

/-- A sum over all entries, of a function that is 0 at the messages that stayed open. -/
theorem sum_new (f : (LocK).S.Ent → GE)
    (h0 : ∀ (a : OldO) (e : ((LocK).S.om (Sum.inl a)).C.J), f ⟨Sum.inl a, e⟩ = 0) :
    ∑ e, f e = ∑ n : (sigOf cs l).Ent, f (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n) :=
  (Fintype.sum_of_injective (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀)
    (newEnt_inj R Hd Sb sl Z A₀ cs l iJ iQ t w₀) _ f
    (fun i hi => by
      rcases i with ⟨a | b, x⟩
      · exact h0 a x
      · exact absurd ⟨⟨b, x⟩, rfl⟩ hi)
    (fun _ => rfl)).symm

/-- **One typed row and the program's row at its place.** -/
theorem typed_iff (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc) (b : (LocK).RowN) (ids : ℕ → ℕ)
    (r : OnBytes.Row) (ht : readE r.target = ((LocK).rowsOf pJK pQK Slf.idf id x).1 b)
    (hv : ∀ n : (sigOf cs l).Ent,
      coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 =
        ((LocK).rowsOf pJK pQK Slf.idf id x).2 b ⟨Sum.inr n.1, n.2⟩)
    (h0 : ∀ (a : OldO) (e : ((LocK).S.om (Sum.inl a)).C.J),
      ((LocK).rowsOf pJK pQK Slf.idf id x).2 b ⟨Sum.inl a, e⟩ = 0) (u : (LocK).S.Msg) :
    (Slf.idf : Slf GE ((LocK).S.Ent → GE) (LocK).S.Ent).Holds
        (((LocK).rowsOf pJK pQK Slf.idf id x).1 b, ((LocK).rowsOf pJK pQK Slf.idf id x).2 b)
        ((LocK).S.ents u) ↔
      TextHolds cs l ids r
        (fun n => (LocK).S.ents u (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n)) := by
  have e : ∑ e, ((LocK).rowsOf pJK pQK Slf.idf id x).2 b e * (LocK).S.ents u e =
      ∑ n : (sigOf cs l).Ent,
        coefAt r (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2 *
          (LocK).S.ents u (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n) := by
    rw [sum_new R Hd Sb sl Z A₀ cs l iJ iQ t w₀ _ (fun a e => by rw [h0 a e, zero_mul])]
    exact Finset.sum_congr rfl fun n _ => by rw [hv n]; rfl
  show ∑ e, ((LocK).rowsOf pJK pQK Slf.idf id x).2 b e * (LocK).S.ents u e = _ ↔ _
  unfold TextHolds
  rw [e, ht]

/-- **All rows of the program's list hold ⇒ the typed claim behind the positions holds.** -/
theorem after_of_text {St : OnBytes.Statement} {old : OnBytes.SingleRows}
    {T : OnBytes.SwitchTarget} {g : ℕ} {anew : Array ℕ} {pos : OnBytes.Positions}
    {y : Array OnBytes.E} {rows : List OnBytes.Row} {W : OnBytes.SwitchFrame}
    {carried : OnBytes.Row} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : R.Kp → ℕ}
    {pl : R.Kp → OnBytes.KeptPlace} {aKept : R.Kp → ℕ} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} (L : Laid St old T g anew pos y rows W carried)
    (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names R.s R.Kp cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK R.s R.Kp cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (rowIn : ∀ κ, row κ < (pl κ).rows)
    (hm : old.masks = 2) (h0 : aM0 = W.parts.maskAt.getD 0 0) (h1 : aM1 = W.parts.maskAt.getD 1 0)
    (Q : ∀ ks, old.kept.toList.mapM (placeOf W) = some ks →
      ClaimOK R.s R.Kp cs l W ids mem row pl old ks)
    (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (X : TieN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x St W ids old pos y mem row pl aOf iOf)
    (hL : (LocK).Lin pJK pQK Slf.idf id) (u : (LocK).S.Msg)
    (hrows : ∀ r ∈ rows, TextHolds cs l ids r
      (fun n => (LocK).S.ents u (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n))) :
    (LocK).After x u := by
  refine (ldLoc_after_rows GE Kc (LocK) _ _ _ _ _ hL x u).2 fun b => ?_
  obtain ⟨r, hr, ht, hv, hz, -⟩ :=
    hands_on_rows R Hd Sb sl Z A₀ cs l iJ iQ t w₀ L F D DK member rowIn hm h0 h1 Q x X b
  exact (typed_iff R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x b ids r ht hv hz u).2
    (hrows r (List.mem_of_getElem? hr))

/-- **The typed claim behind the positions holds ⇒ all rows of the program's list hold.** -/
theorem text_of_after {St : OnBytes.Statement} {old : OnBytes.SingleRows}
    {T : OnBytes.SwitchTarget} {g : ℕ} {anew : Array ℕ} {pos : OnBytes.Positions}
    {y : Array OnBytes.E} {rows : List OnBytes.Row} {W : OnBytes.SwitchFrame}
    {carried : OnBytes.Row} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : R.Kp → ℕ}
    {pl : R.Kp → OnBytes.KeptPlace} {aKept : R.Kp → ℕ} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} (L : Laid St old T g anew pos y rows W carried)
    (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names R.s R.Kp cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK R.s R.Kp cs l iJ iQ W ids mem row pl aKept)
    (hm : old.masks = 2) (h0 : aM0 = W.parts.maskAt.getD 0 0) (h1 : aM1 = W.parts.maskAt.getD 1 0)
    (Q : ∀ ks, old.kept.toList.mapM (placeOf W) = some ks →
      ClaimOK R.s R.Kp cs l W ids mem row pl old ks)
    (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (X : TieN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x St W ids old pos y mem row pl aOf iOf)
    (A : SlotsAll R.Kp W mem row pl) (H : Held St W aOf iOf)
    (hd : pos.draws.toList.length = (LocK).t)
    (hL : (LocK).Lin pJK pQK Slf.idf id) (u : (LocK).S.Msg) (hA : (LocK).After x u) :
    ∀ r ∈ rows, TextHolds cs l ids r
      (fun n => (LocK).S.ents u (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n)) := by
  intro r hr
  obtain ⟨m, hm', hrm⟩ := List.getElem_of_mem hr
  rw [hands_on_count L hm hd] at hm'
  obtain ⟨b, hb⟩ := rowNo_onto (s := R.s) A H m hm'
  obtain ⟨r', hr', ht, hv, hz, -⟩ :=
    hands_on_rows R Hd Sb sl Z A₀ cs l iJ iQ t w₀ L F D DK A.member A.rowIn hm h0 h1 Q x X b
  have e : r' = r := by
    have h2 : rows[m]? = some r' := (congrArg (fun i => rows[i]?) hb).symm.trans hr'
    rw [List.getElem?_eq_getElem (by rw [hands_on_count L hm hd]; exact hm'), hrm] at h2
    exact (Option.some.inj h2).symm
  subst e
  exact (typed_iff R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x b ids r' ht hv hz u).1
    ((ldLoc_after_rows GE Kc (LocK) _ _ _ _ _ hL x u).1 hA b)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.typed_iff
#print axioms VerifiableInference.Desc.First.K2Hands.after_of_text
#print axioms VerifiableInference.Desc.First.K2Hands.text_of_after
