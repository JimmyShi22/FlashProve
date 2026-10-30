-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountLedger.lean: THE ROW `shared_joint_count` TAKEN APART INTO ITS
DEBTS, ON THE PLAIN ROAD, AT THE CAP: one named debt a block, and the proof that the debts together
ARE the row's fifth form (Johnson/Desc/Sound/SharedJointCountRowE.lean). Definitions, statements
written as `def … : Prop`, and their proofs.

Why. Since the pieces carry the cap, "a kind's own
errors are shares of at most 1 / 2 ^ 128 of the written rounds' challenges" would stand, unnamed, in
twelve sets of files: a debt that nobody sees. Here it has a name and a place for each block
(`EachOwnBelow`), beside the block's law at these own errors; and what comes by make is taken off
the kinds' files.

What is said.
  `OwnErrs`: a kind's own errors for block number i, at its piece: A LETTER of the ledger.
  `EachOwnBelow k own`: DEBT (b), a block: own i p is below 2⁻¹ ^ k.
  `EachLawsBNOwn`: `EachLawsBN` (Johnson/Desc/Sound/KeysByMake.lean) at own i p in place of p.err.
  `eachLawsBN_atCap`: pieces that carry the cap + (b) + the laws at the own errors ⟹ `EachLawsBN`.
    Two calls a block: `Err.le_cap_of_below_inv` (Iop/ErrCap.lean) and
    `LeadsBN.mono_err` (Johnson/Desc/Plain/KeyAlone.lean).
  `extOf Ns p l e₀`: the row's named extractor, made of an e₀ that READS THE ACTING PART ALONE.
  `EachPlainShOwn`, `eachPlainSh_atCap`: the same for `EachPlainSh`
    (Johnson/Desc/Sound/SharedJoinPlain.lean): a kind's plain law FOR ONE STATEMENT, of the shared
    items alone.
  `sameOut_false`: A FIND. Other rules for the whole shared chain (`FrontPays`, SharedCertain.lean;
    `FrontLost`, `SharedChainLostBoth`, `SharedChainLeadsBN`: not in this library) ask of the front block "it puts out
    what it was given": ∀ a τ b, out a τ = some b → b = a. THAT PREMISE IS FALSE AT EVERY REAL CHAIN.
    What a piece leaves of the oracles is the library's stage's (`sLeft`): at a tree that is not yet
    sent behind the block THE EMPTY COLUMN, whatever stood there in front (`out_clears_unsent`). And
    whether a lifted block says yes hangs on the acting part alone, which holds no such tree. So a
    front block that says yes anywhere says yes at a statement with a column there that is not
    empty, and puts out another statement. Premises: the block hands its acting part on; it says
    yes once; the frame lists a tree with a number from the block's base on, and the stretch's
    transcript sends nothing there. SO THESE FOUR RULES ARE EMPTY AT A REAL CHAIN AS THEY STAND.
  `act_stays`: what IS so: where a piece puts out b at a and keeps the record, the acting part up
    to the piece's base is the same at b and at a.
  `FrontRides`: the front block's debt on what a slot has of its own, in the form in which the
    blocks behind the point owe it (`EachRides`): for certain, the slot's own condition goes on
    and the own items ride back.
  `SameBelow`, `frontRides_of_below`: THAT DEBT CAN BE MET (the old one could not): if the slot's own
    condition Oc and the meanings of the own items that are open at the chain's start read the
    oracles through the stored table and the trees with a number below lo alone (`SameBelow`: the
    first chain's trees: so the table's test `NumbersS.sorted` means them), then a front block that
    keeps the record, with lo ≤ its base, has `FrontRides`: by `cellStays`,
    `colStays` (Johnson/Desc/Sound/StringsStay.lean). Whether the letters' fillings read so is
    left to the files that fill them.
  `frontLeadsBN`: the front block has the row's clause at every list of errors, for certain: FROM
    "it keeps the record" (b.1 = a.1), "it sends no tree", the book-keeping's Bool, `FrontRides`.
    Else it follows `frontLost` (SharedChainLostProofs.lean: not in this library).
  `PointOwn`: "LIN point" has the row's clause AT δK + N · δO ITSELF, from the library's typed point:
    `PointAtRow` (Johnson/Desc/Sound/PointAtRow.lean) with the block's errors out of the statement.
  `LedgerPays`: for any row f :: pt :: q :: r of pieces: THE DEBTS ⟹ the row's last clause.
  `RowOfLedger`: AT A DESCRIPTION: ⟹ `SharedJointCountRowE`; "tiled", "lifted", "no tree below lo"
    come by make from `OfDesc`, `Fits` and one test on the data.

THE LEDGER, as `RowOfLedger` has it. BY MAKE OR BY A TEST ON DATA: OfDesc · Fits · the shared rounds
open no tree below t₁ · Ns.lo = t₁ · the shared chain has a front block, a point and at least one
block more · each piece's errors are the cap. THE TABLE's: ExtNamed. THE FRONT BLOCK's (the frame's
files): it keeps the record · it sends no tree (pt.base = f.base) · the book-keeping's Bool at 0
gives that at 1 · what a slot has of its own rides (`FrontRides`). "LIN point"'s (K14's files): ITS LAW IN TWO PARTS at own 1 pt, and (b)
there: THE ONE PLACE WHERE N ENTERS AN ERROR. EACH BLOCK BEHIND (K1's, K14's, K12's files, the files
on the chains' ends): its plain law for one statement at own k x · (b) · what rides, for certain.

Who reads each letter. own: no verifier; the kinds' Lean files. e₀: no verifier; the table's Lean
files. N: the files' own number of slots: THE TOP TAKES THE ROW AT THAT TERM: here a letter.
Every "there is", walked. None of its own. In `LeadsBN`: the split of the errors; the two games.
Limits. RULES: they would stay proved if the protocol were otherwise: THEY CLOSE NO ROW. No debt is
paid here but the front block's clause (under its four facts). At a written round with fewer than
2 ^ 128 challenges the cap is 0: (b) then asks own = 0 there: right at a round that only hears;
whether every shared round with a real error has that many challenges is a test on the plan, owed.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountRowE
import Johnson.Desc.Sound.SharedJoinPlain
import Johnson.Desc.Sound.SharedCertainProofs
import Johnson.Desc.Sound.PointAtRow
import Johnson.Desc.Plain.KeyAlone
import Johnson.Desc.Sound.StageCut
import Johnson.Desc.Sound.StringsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open VerifiableInference.Desc.Shared

/-- A kind's own errors for the block number i, at its piece. -/
abbrev OwnErrs (C : CK) (F : Frame) (S Cl W : Type) : Type :=
  ℕ → (p : Piece C F S Cl W) → Err (uLT C p.ds)

section General
variable {S Cl W κ : Type} {C : CK} {F : Frame}

/-- **Debt (b), a block**: the kind's own errors are shares of at most 1 / 2 ^ k of the written
rounds' challenges. -/
def EachOwnBelow (k : ℕ) (own : OwnErrs C F S Cl W) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l => Err.Below (own i p) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧ EachOwnBelow k own (i + 1) l

/-- What is left to the kinds' files of a shared chain, at the kinds' own errors. -/
def EachLawsBNOwn (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ) (own : OwnErrs C F S Cl W) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.ior.red.LeadsBN (key i) (on i) (Q i) N (own i p) ∧ (∀ a b, on i a → Q i a b → on (i + 1) b) ∧
      EachLawsBNOwn key on Q N own (i + 1) l

theorem le_err_of_capped (k : ℕ) (p : Piece C F S Cl W) (e : Err (uLT C p.ds))
    (hc : p.err = Err.cap k (uLT C p.ds)) (hb : Err.Below e ((2 : ℝ≥0∞)⁻¹ ^ k)) :
    Err.le e p.err := by
  rw [hc]
  exact Err.le_cap_of_below_inv k e hb

/-- **The laws at the kinds' own errors are the laws at the cap.** -/
theorem eachLawsBN_atCap (k : ℕ) (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ) (own : OwnErrs C F S Cl W) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachCapped k l → EachOwnBelow k own i l →
      EachLawsBNOwn key on Q N own i l → EachLawsBN key on Q N i l
  | [], _, _, _, _ => trivial
  | p :: l, i, hc, hb, h =>
    ⟨h.1.mono_err (le_err_of_capped k p (own i p) (hc p (List.mem_cons_self ..)) hb.1), h.2.1,
      eachLawsBN_atCap k key on Q N own l (i + 1) (fun q hq => hc q (List.mem_cons_of_mem _ hq))
        hb.2 h.2.2⟩

/-- What a piece leaves of the oracles: the stored table as it is, and what its stage leaves. -/
theorem out_strs (p : Piece C F S Cl W) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) : b.2 = (a.2.1, sLeft C (stg F p.base p.ds) a.2 τ) := by
  have h' : (p.ior.out a.1 a.2 τ).map (fun xo => (xo, p.ior.imp a.2 τ)) = some b := hb
  obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 h'
  rfl

/-- **At a tree that is not sent behind the block, the block leaves the empty column.** -/
theorem out_clears_unsent (p : Piece C F S Cl W) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (j x : ℕ) (pos : PosL F.all)
    (hp : posL F.all j x = some pos) (hj : ¬ j < p.base)
    (hn : colAtST C p.ds τ (j - p.base) x = none) : b.2.2 pos = [] := by
  rw [out_strs p a b τ hb]
  show sLeft C (stg F p.base p.ds) a.2 τ pos = []
  rw [sLeft_at C F p.ds p.base a.2 τ j x pos hp, sCol_eq, if_neg hj, hn]
  rfl

/-- **Where a piece keeps the record, the acting part up to its base stays.** -/
theorem act_stays {S₀ : Type} (get : S → S₀) (lo : ℕ) (p : Piece C F S Cl W) (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b) (hr : b.1 = a.1) :
    (actAt F get lo p.base).2 b = (actAt F get lo p.base).2 a := by
  have e := out_strs p a b τ hb
  show (get b.1, b.2.1, fun j x => if lo ≤ j ∧ j < p.base then (posL F.all j x).map b.2.2 else none)
    = (get a.1, a.2.1, fun j x => if lo ≤ j ∧ j < p.base then (posL F.all j x).map a.2.2 else none)
  rw [hr, e]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext j x
  show (if lo ≤ j ∧ j < p.base then
      (posL F.all j x).map (sLeft C (stg F p.base p.ds) a.2 τ) else none) =
    (if lo ≤ j ∧ j < p.base then (posL F.all j x).map a.2.2 else none)
  by_cases h : lo ≤ j ∧ j < p.base
  · rw [if_pos h, if_pos h]
    cases hp : posL F.all j x with
    | none => rfl
    | some q =>
      show some (sLeft C (stg F p.base p.ds) a.2 τ q) = some (a.2.2 q)
      rw [sLeft_at C F p.ds p.base a.2 τ j x q hp, sCol_eq, if_pos h.2, hp]
      rfl
  · rw [if_neg h, if_neg h]

/-- **"IT PUTS OUT WHAT IT WAS GIVEN" IS FALSE** of a block that hands its acting part on and says
yes once, where the frame lists a tree that is not sent behind the block. -/
theorem sameOut_false {S₀ : Type} (get : S → S₀) (lo : ℕ) (f : Piece C F S Cl W) (act' : BKey F S)
    (hh : f.HandsAct (actAt F get lo f.base) act') (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT C f.ds)) (hb : f.ior.red.out a τ = some b) (j x : ℕ) (pos : PosL F.all)
    (hp : posL F.all j x = some pos) (hj : ¬ j < f.base)
    (hn : colAtST C f.ds τ (j - f.base) x = none) :
    ¬ ∀ a τ b, f.ior.red.out a τ = some b → b = a := by
  classical
  intro hsame
  obtain ⟨G, hG⟩ := hh
  have hact : (actAt F get lo f.base).2 (a.1, (a.2.1, fun q => if q = pos then [0] else a.2.2 q)) =
      (actAt F get lo f.base).2 a := by
    show (get a.1, a.2.1, fun j' x' => if lo ≤ j' ∧ j' < f.base then
        (posL F.all j' x').map (fun q => if q = pos then [0] else a.2.2 q) else none) =
      (get a.1, a.2.1, fun j' x' => if lo ≤ j' ∧ j' < f.base then
        (posL F.all j' x').map a.2.2 else none)
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext j' x'
    show (if lo ≤ j' ∧ j' < f.base then
        (posL F.all j' x').map (fun q => if q = pos then [0] else a.2.2 q) else none) =
      (if lo ≤ j' ∧ j' < f.base then (posL F.all j' x').map a.2.2 else none)
    by_cases h : lo ≤ j' ∧ j' < f.base
    · rw [if_pos h, if_pos h]
      cases hq : posL F.all j' x' with
      | none => rfl
      | some q =>
        show some (if q = pos then [0] else a.2.2 q) = some (a.2.2 q)
        rw [if_neg]
        intro hqp
        rw [hqp] at hq
        have e1 := (posL_spec F.all j' x' pos hq).1
        have e2 := (posL_spec F.all j x pos hp).1
        omega
    · rw [if_neg h, if_neg h]
  have h1 : (f.ior.red.out (a.1, (a.2.1, fun q => if q = pos then [0] else a.2.2 q)) τ).map act'.2 =
      (f.ior.red.out a τ).map act'.2 := by
    rw [hG, hG, hact]
  rw [hb] at h1
  obtain ⟨b', hb', -⟩ := Option.map_eq_some_iff.1 h1
  have hc := out_clears_unsent f _ b' τ hb' j x pos hp hj hn
  rw [hsame _ τ b' hb'] at hc
  have hc' : (if pos = pos then ([0] : List UInt64) else a.2.2 pos) = [] := hc
  rw [if_pos rfl] at hc'
  cases hc'

-- at a stretch without a round (so a front block's) nothing is sent: the last premise holds
example (τ : Iop.Tr (uLT C [])) (n x : ℕ) : colAtST C [] τ n x = none := rfl

end General

section Table
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (Ns : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (e₀ : ℕ → ActV S₂ Fr → Wt → Wt)

/-- The row's named extractor, made of one that reads the acting part alone. -/
def extOf (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str) (w : Wt) : Wt :=
  e₀ k (keyAt Prod.snd Ns.lo p l k a) w

/-- Each kind's plain law for one statement, of the shared items alone, at its own errors. -/
def EachPlainShOwn (own : OwnErrs C Fr (P₁ × S₂) Cl Wt) :
    ℕ → List (Piece C Fr (P₁ × S₂) Cl Wt) → Prop
  | _, [] => True
  | k, x :: m =>
    x.ior.red.Leads (onQ₂ Ns Pm Oc split p l k)
        (fun a b => stepV Ns Mg Pm split p l e₀ k ((actQ Ns p l k).2 a) ((actQ Ns p l (k + 1)).2 b))
        (own k x) ∧
      EachPlainShOwn own (k + 1) m

theorem eachPlainSh_atCap (c : ℕ) (own : OwnErrs C Fr (P₁ × S₂) Cl Wt) :
    ∀ (m : List (Piece C Fr (P₁ × S₂) Cl Wt)) (k : ℕ), EachCapped c m → EachOwnBelow c own k m →
      EachPlainShOwn Ns Mg Pm Oc split p l e₀ own k m → EachPlainSh Ns Mg Pm Oc split p l e₀ k m
  | [], _, _, _, _ => trivial
  | x :: m, k, hc, hb, h =>
    ⟨h.1.mono_err (le_err_of_capped c x (own k x) (hc x (List.mem_cons_self ..)) hb.1),
      eachPlainSh_atCap c own m (k + 1) (fun q hq => hc q (List.mem_cons_of_mem _ hq)) hb.2 h.2⟩

/-- **For certain, at the front block: what each slot has of its own rides.** -/
def FrontRides : Prop :=
  ∀ a τ b, onQ₂ Ns Pm Oc split p l 0 a → p.ior.red.out a τ = some b →
    Oc b.1.1 (strsOf Fr b.2) ∧ ∀ w, relOwn Ns Mg 1 b w → relOwn Ns Mg 0 a w

/-- Two readings of the oracles agree at the stored table and at the trees below lo. -/
def SameBelow (lo : ℕ) (y y' : Strs) : Prop := y.cell = y'.cell ∧ ∀ j, j < lo → y.col j = y'.col j

/-- **The front block's debt on what rides can be met**: where what a slot has of its own reads the
stored table and the trees below lo alone. -/
theorem frontRides_of_below (hlo : Ns.lo ≤ p.base)
    (hrec : ∀ a τ b, p.ior.red.out a τ = some b → b.1 = a.1)
    (hOc : ∀ x y y', SameBelow Ns.lo y y' → Oc x y → Oc x y')
    (hOwn : ∀ i ∈ ownAt 0, ∀ x s y y' w, SameBelow Ns.lo y y' →
      ItemS.holdsOwn Ns Mg i x s y w → ItemS.holdsOwn Ns Mg i x s y' w) :
    FrontRides Ns Mg Pm Oc split p l := by
  intro a τ b ha hb
  have e := out_strs p a b τ hb
  have hr := hrec a τ b hb
  have hs : SameBelow Ns.lo (strsOf Fr a.2) (strsOf Fr b.2) := by
    rw [e]
    refine ⟨rfl, fun j hj => ?_⟩
    funext x
    exact (colStays C Fr p.base p.ds a.2 τ j x (Nat.lt_of_lt_of_le hj hlo)).symm
  refine ⟨?_, fun w hw i hi => ?_⟩
  · rw [hr]
    exact hOc _ _ _ hs ha.2
  · have h1 : ItemS.holdsOwn Ns Mg i b.1.1 b.1.2 (strsOf Fr b.2) w := hw i hi
    rw [hr] at h1
    exact hOwn i hi _ _ _ _ w ⟨hs.1.symm, fun j hj => (hs.2 j hj).symm⟩ h1

/-- **The front block has the row's clause, for certain, at every list of errors.** -/
theorem frontLeadsBN (f pt : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (ext : ℕ → (P₁ × S₂) × Fr.E.Str → Wt → Wt) (n : ℕ) (ε : Err (uLT C f.ds))
    (hrec : ∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) (hbase : pt.base = f.base)
    (hshape : ∀ s, Pm.shape 0 s = true → Pm.shape 1 s = true) (hext : ∀ a w, ext 0 a w = w)
    (hride : FrontRides Ns Mg Pm Oc split f (pt :: r)) :
    f.ior.red.LeadsBN (keyAt Prod.snd Ns.lo f (pt :: r) 0) (onQ₂ Ns Pm Oc split f (pt :: r) 0)
      (stepAt Ns Mg Pm Oc split f (pt :: r) ext 0) n ε := by
  refine (Reduction.LeadsK.of_sure (K := f.ior.red) _ ε fun a τ b ha hb => ?_).bothN n
  have hact : (actQ Ns f (pt :: r) 1).2 b = (actQ Ns f (pt :: r) 0).2 a := by
    show (actAt Fr Prod.snd Ns.lo pt.base).2 b = (actAt Fr Prod.snd Ns.lo f.base).2 a
    rw [hbase]
    exact act_stays Prod.snd Ns.lo f a b τ hb (hrec a τ b hb)
  obtain ⟨hoc, hown⟩ := hride a τ b ha hb
  show onQ₂ Ns Pm Oc split f (pt :: r) 1 b ∧
    ∀ w, relQ₂ Ns Mg split f (pt :: r) 1 b w → relQ₂ Ns Mg split f (pt :: r) 0 a (ext 0 a w)
  refine ⟨⟨fun c hc => ?_, hoc⟩, fun w hw => ?_⟩
  · rw [promsAt_one] at hc
    have h0 := ha.1
    rcases List.mem_cons.1 hc with rfl | hc
    · have := h0 .tablePromise (by rw [promsAt_zero]; exact List.mem_cons_self ..)
      rw [hact]
      exact this
    · obtain rfl := List.mem_singleton.1 hc
      have := h0 (.shape 0)
        (by rw [promsAt_zero]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      rw [hact]
      exact hshape _ this
  · rw [hext]
    refine ⟨fun i hi => ?_, hown w hw.2⟩
    have h1 := hw.1 i (Or.inl ⟨hi, fun hin => by
      have := hin.2
      rw [rowAtS_zero] at this
      cases this⟩)
    have h2 : muQ Ns Mg f (pt :: r) i 1 ((actQ Ns f (pt :: r) 1).2 b) w := h1
    rw [hact] at h2
    exact h2

end Table

/-- **"LIN point" has the row's clause at δK + N · δO itself**, by the carriage of the typed point's
two games. The letters and the premises are `PointAtRow`'s, but for the block's own errors. -/
def PointOwn : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
    [Fintype Y] (P : Cb.LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (εf N : ℕ) (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (Ns : NumbersS)
    (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
    (f pt : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (ext : ℕ → (P₁ × S₂) × Fr.E.Str → Wt → Wt)
    (G : S₂ × (oneExternalString (2 ^ Fr.a) SgX).Str × (ℕ → ℕ → Option (List UInt64)) →
      CarryS (uLT C pt.ds) P.pt.red.shape)
    (fk : S₂ × (oneExternalString (2 ^ Fr.a) SgX).Str × (ℕ → ℕ → Option (List UInt64)) →
      (ι → P.Sy) × P.D.X.Rec)
    (δK δO : Err (uLT C pt.ds)) (rd : (P₁ × S₂) × Fr.E.Str → P.X1 × P.E1.Str),
    P.FoldErr on0 εf →
    (∀ k, (G k).Fits ((εf * Fintype.card E ^ P.D.klo, ()) : ℕ × Unit) δK) →
    (∀ k, (G k).Fits
      (((P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1), ()) : ℕ × Unit) δO) →
    (∀ a, P.k1 (rd a) = fk (keyAt Prod.snd Ns.lo f (pt :: r) 1 a)) →
    (∀ a, onQ₂ Ns Pm Oc split f (pt :: r) 1 a → (P.j1 on0).on (rd a)) →
    (∀ a τ b, onQ₂ Ns Pm Oc split f (pt :: r) 1 a → pt.ior.red.out a τ = some b →
      ∃ τ' b', (G (keyAt Prod.snd Ns.lo f (pt :: r) 1 a)).tr τ = some τ' ∧
        P.pt.red.out (rd a) τ' = some b' ∧
        (((P.j2 on0).on b' ∧ ∀ w', (P.j2 on0).relR b' w' → (P.j1 on0).relR (rd a) w'.2) →
          stepAt Ns Mg Pm Oc split f (pt :: r) ext 1 a b)) →
    pt.ior.red.LeadsBN (keyAt Prod.snd Ns.lo f (pt :: r) 1) (onQ₂ Ns Pm Oc split f (pt :: r) 1)
      (stepAt Ns Mg Pm Oc split f (pt :: r) ext 1) N (Err.add δK (Err.times N δO))

theorem pointOwn : PointOwn := by
  intro E ι κ J Y _ _ _ _ _ _ _ P on0 εf N P₁ S₂ Cl Wt C Fr Ns Mg Pm Oc split f pt r ext G fk δK δO
    rd hF hFK hFO hk hon hout
  exact leadsBN_carryS pt.ior.red P.pt.red _ P.k1 G fk _ _ δK δO N _ (Err.le_refl _) hFK hFO rd hk _
    (P.j1 on0).on _ _ hon hout (P.pt_leadsB on0 εf hF)

/-- **THE DEBTS TOGETHER ARE THE ROW's LAST CLAUSE**: for any row f :: pt :: q :: r of pieces. -/
def LedgerPays : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (Ns : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool) (n : ℕ)
    (f pt q : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (e₀ : ℕ → ActV S₂ Fr → Wt → Wt) (own : OwnErrs C Fr (P₁ × S₂) Cl Wt),
    Tiled q r →
    (∀ x ∈ q :: r, ∃ b₀ : Block S₂ Cl, x.b = b₀.lift Prod.snd fun t s => (t.1, s)) →
    (∀ x ∈ q :: r, ∀ d ∈ x.ds, ∀ j ∈ d.opens, Ns.lo ≤ j) →
    EachCapped 128 (pt :: q :: r) →
    EachOwnBelow 128 own 1 (pt :: q :: r) →
    (∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) → pt.base = f.base →
    (∀ s, Pm.shape 0 s = true → Pm.shape 1 s = true) →
    FrontRides Ns Mg Pm Oc split f (pt :: q :: r) →
    (∀ a w, extOf Ns f (pt :: q :: r) e₀ 0 a w = w) →
    pt.ior.red.LeadsBN (keyAt Prod.snd Ns.lo f (pt :: q :: r) 1)
      (onQ₂ Ns Pm Oc split f (pt :: q :: r) 1)
      (stepAt Ns Mg Pm Oc split f (pt :: q :: r) (extOf Ns f (pt :: q :: r) e₀) 1) n (own 1 pt) →
    EachPlainShOwn Ns Mg Pm Oc split f (pt :: q :: r) e₀ own 2 (q :: r) →
    EachRides Ns Mg Pm Oc split f (pt :: q :: r) e₀ 2 (q :: r) →
    EachLawsBN (keyAt Prod.snd Ns.lo f (pt :: q :: r)) (onQ₂ Ns Pm Oc split f (pt :: q :: r))
      (stepAt Ns Mg Pm Oc split f (pt :: q :: r) (extOf Ns f (pt :: q :: r) e₀)) n 0
      (f :: pt :: q :: r)

theorem ledgerPays : LedgerPays := by
  intro P₁ S₂ Cl Wt C Fr Ns Mg Pm Oc split n f pt q r e₀ own ht hb ho hc hbel f1 f2 f4 f5 hx hpt hp
    hr
  have h10 := sharedJoinPlain P₁ S₂ Cl Wt C Fr Ns Mg Pm Oc split n f pt q r e₀ ht hb ho
    (eachPlainSh_atCap Ns Mg Pm Oc split f (pt :: q :: r) e₀ 128 own (q :: r) 2
      (fun x hx' => hc x (List.mem_cons_of_mem _ hx')) hbel.2 hp) hr
  exact ⟨frontLeadsBN Ns Mg Pm Oc split f pt (q :: r) _ n f.err f1 f2 f4 hx f5, fun _ _ _ h => h.1,
    hpt.mono_err (le_err_of_capped 128 pt (own 1 pt) (hc pt (List.mem_cons_self ..)) hbel.1),
    fun _ _ _ h => h.1, h10⟩

/-- **AT A DESCRIPTION: THE DEBTS TOGETHER ARE THE ROW's FIFTH FORM.** -/
def RowOfLedger : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ Wt : Type) (F : FileDescription (X × Rec))
    (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS) (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt)
    (Pm : PromMeaning F.S₂) (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool) (N : ℕ)
    (pt q : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)
    (r : List (Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt))
    (e₀ : ℕ → ActV F.S₂ (frameAt D all D.key₂ (atDesc F T).ft₂) → Wt → Wt)
    (same : Comp → Wt → Wt → Prop)
    (own : OwnErrs C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt),
    OfDesc F T → (atDesc F T).Fits → (∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) → Ns.lo = D.t₁ →
    (atDesc F T).l₂ = pt :: q :: r →
    EachCapped 128 ((atDesc F T).p₂ :: pt :: q :: r) →
    ExtNamed split (extOf Ns (atDesc F T).p₂ (pt :: q :: r) e₀) same →
    EachOwnBelow 128 own 1 (pt :: q :: r) →
    (∀ a τ b, (atDesc F T).p₂.ior.red.out a τ = some b → b.1 = a.1) →
    pt.base = (atDesc F T).p₂.base →
    (∀ s, Pm.shape 0 s = true → Pm.shape 1 s = true) →
    FrontRides Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: q :: r) →
    pt.ior.red.LeadsBN (keyAt Prod.snd Ns.lo (atDesc F T).p₂ (pt :: q :: r) 1)
      (onQ₂ Ns Pm Oc split (atDesc F T).p₂ (pt :: q :: r) 1)
      (stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: q :: r)
        (extOf Ns (atDesc F T).p₂ (pt :: q :: r) e₀) 1) N (own 1 pt) →
    EachPlainShOwn Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: q :: r) e₀ own 2 (q :: r) →
    EachRides Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: q :: r) e₀ 2 (q :: r) →
    SharedJointCountRowE C D all X Rec X₁ X₂ Wt F T Ns Mg Pm Oc split N
      (extOf Ns (atDesc F T).p₂ (atDesc F T).l₂ e₀) same

theorem rowOfLedger : RowOfLedger := by
  intro C D all X Rec X₁ X₂ Wt F T Ns Mg Pm Oc split N pt q r e₀ same own hO hf opens hlo hl hc hx
    hbel f1 f2 f4 f5 hpt hp hr
  obtain ⟨-, -, hb⟩ := liftedAtDesc C D all (X × Rec) X₁ X₂ Wt F T hO
  have ht := hf.tiled₂
  have hd := hf.data₂
  rw [hl] at hb ht hd
  unfold SharedJointCountRowE
  rw [hl, ← hlo]
  refine ⟨rfl, hc, hx, ?_⟩
  exact ledgerPays _ _ _ _ C _ Ns Mg Pm Oc split N (atDesc F T).p₂ pt q r e₀ own ht.2.2.2.2.2.2.2.2
    (fun x hx' => hb x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx')))
    (fun x hx' d hd' j hj => hlo ▸ opens d
      (hd ▸ mem_rowData (atDesc F T).p₂ (pt :: q :: r) x
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx')) d hd') j hj)
    (fun x hx' => hc x (List.mem_cons_of_mem _ hx')) hbel f1 f2 f4 f5
    (fun a w => hx.1 0 (by cases split <;> rfl) a w) hpt hp hr

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.eachLawsBN_atCap
#print axioms VerifiableInference.Desc.Sound.eachPlainSh_atCap
#print axioms VerifiableInference.Desc.Sound.out_clears_unsent
#print axioms VerifiableInference.Desc.Sound.act_stays
#print axioms VerifiableInference.Desc.Sound.sameOut_false
#print axioms VerifiableInference.Desc.Sound.frontRides_of_below
#print axioms VerifiableInference.Desc.Sound.frontLeadsBN
#print axioms VerifiableInference.Desc.Sound.pointOwn
#print axioms VerifiableInference.Desc.Sound.ledgerPays
#print axioms VerifiableInference.Desc.Sound.rowOfLedger
