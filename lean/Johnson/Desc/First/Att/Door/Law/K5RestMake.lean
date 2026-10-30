-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5RestMake.lean: kind K5: THE SIXTEEN FIELDS "BY THE MAKE" OF K5Rest (K5AtMgPaid.lean), AS THEOREMS AT THE COMPOSED MEANING's CLOSED CONSTANT (Johnson/P5J/MgAtAll.lean), under the one head h : AtMgA o Z D r Zp Np cF x.

Why. For a member of K5Rest at the closed term these fields must be theorems there. Each is a law on a parameter's make: true at all states or at none.

THE LETTERS: Mg := mgPlusAll h Ld Ms · Mg0 := mgB0 · D := h.𝔇.pubD · Dn := h.𝔇.sent · arr | smp | ms | decT := h.𝔇's · in0 := mgB0.inOrder · D13 := d13 h.𝔇 (so D13.rw is h.𝔇.rw13: the reader through the book) ·
Wv := At.X Zp · links := h.𝔇.links · rad := h.𝔇.l3.rad · seat := seatAll h x₁ · smpR := smpRAll h x₁ (A CHOICE) · lk := At.lk Zp · claimC := K3Lot.ofForm · Hd := Holds · bsW := h.𝔇.H.base · dP := h.𝔇.digitsPart ·
body := bodyAll h.𝔇. FREE: Ld · Ms · bs · g · before · a · x₁ · pl · O · Q · Lk · same · blk · nm · Zof.

Main names:
  `K5RestAll`: K5Rest at these letters. `seatAll`, `smpRAll`: the two letters that are ours to pick.
  `bodyAll_blind`: the body of a constraint reads the state through H.req and headPart alone.
  `baseP_all` (under K5Table.openQ's text) · `baseIn_all` · `baseMakes_all` · `decTq_all` · `smpq_all` · `rwq_all` · `smpIs_all` · `constrIsPlus_all` · `bodySmall_all` (under profile 4) · `digitsBack_all` · `bodyBack_all` ·
  `smpBySeat_all` · `runsIs_all` · `mHIs_all` · `rdIs_all` (K5AtConstant.lean's) · `clForm_lot` (K5RestBlind.lean's).
  `rest_make`: THE CHECK: a member of K5RestAll with these sixteen fields laid over it: so each theorem has its field's type.
Is it empty here? Under the head: A MEMBER OF IT IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). The theorems themselves ask nothing of a state.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5MgIsAll
import Johnson.Desc.First.Att.Door.Law.K5RestBlind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (headLink)
open OnBytes.Road.L5 (Zs)
open P5J (AtMgA mgAtAll TS)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **The body of a constraint reads the state through H.req and headPart alone; the strings through headPart alone.** -/
theorem bodyAll_blind {a b : P × S} (hr : 𝔇.H.req b = 𝔇.H.req a)
    (hh : ∀ p i y y' w, 𝔇.headPart p i b y' w = 𝔇.headPart p i a y w) (n : ℕ) (p : First.Part) (i : IdxQ) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) : bodyAll 𝔇 n p i b y' w = bodyAll 𝔇 n p i a y w := by
  unfold bodyAll
  rw [hr, hh p i y y' w]

/-- The reader of the pile of pending rows rides over the kind's lay. -/
theorem rwq_any (π : P) (s : S) (a : AttOwn) (h : _) (G : Fork) :
    (d13 𝔇).rw (π, behind s a h G) = (d13 𝔇).rw (π, s) := rwq_book 𝔇.arr 𝔇.mat13 π s a h G

/-- An odd number is not the output head's, at profile 4. -/
theorem notHead_any (h4 : X.p4 = true) (g : ℕ) : 2 * g + 1 ≠ headLink X := (odd_facts (W := X) (g := g) h4).1

end

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

/-- The pin's seats: the lookup arguments' own. -/
noncomputable def seatAll (x₁ : Look.Place) : Fin (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length → ℕ × ℕ :=
  fun j => h.𝔇.l3.seat x₁.link false j.1

/-- **The filled pin's reader of samples: the choice.** -/
noncomputable def smpRAll (x₁ : Look.Place) : Array OnBytes.Oracle × OnBytes.TreeBook →
    (i : Fin (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length) →
      Option ((sigOf h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link)).om i).Smp :=
  smpROf (P5J.At.cs Zp) (P5J.At.seats Zp) (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link) (seatAll h x₁)

/-- **K5Rest at the closed letters.** -/
abbrev K5RestAll {Fr : Frame} (Ld : Laid) (Ms : List OracleShape) (bs g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x₁ : Look.Place)
    (pl : VerifiableInference.Desc.Place) (O : List Item) (Q : List Pub) (Lk : Link S Claim) (same : S → S → Bool) (blk : Block S Claim)
    (nm : String) (Zof : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Zs) : Prop :=
  K5Rest (Fr := Fr) (mgPlusAll h Ld Ms) mgB0 h.𝔇.pubD h.𝔇.sent h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT mgB0.inOrder Ld Ms (d13 h.𝔇) bs (P5J.At.X Zp) g before a
    x₁ h.𝔇.links pl h.𝔇.l3.rad O Q (seatAll h x₁) (smpRAll h x₁) (P5J.At.lk Zp) Lk same blk K3Lot.ofForm nm
    VerifiableInference.OnPublicFiles.Flat.Holds h.𝔇.H.base h.𝔇.digitsPart (bodyAll h.𝔇) Zof

theorem baseP_all (g : ℕ) (Q : List Pub)
    (hQ : ∀ q ∈ Q, q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨ q = .more (some (2 * g + 1)) "ledger.treesAre" ∨
      q = .more (some (2 * g + 1)) "K5.lookLeft") :
    ∀ q a, (q ∈ Q ∨ q ∈ made3 (2 * g + 1)) → isWideQ q = false → (∀ m', q ≠ .left m') → (∀ m', q ≠ .leftOn m') → mgB0.pubP q a :=
  fun q _ hq hw hl _ => said_touched (2 * g + 1) Q hQ q hq hw hl

theorem baseIn_all : ∀ π s a h' G, s.here = .att a → mgB0.inOrder (π, s) = true → mgB0.inOrder (π, behind s a h' G) = true :=
  baseIn_base

theorem baseMakes_all (links : List ModelPart) (pl : VerifiableInference.Desc.Place) : (mgB0.more.rows links pl).makes = [] :=
  baseMakes_base links pl

theorem decTq_all : ∀ π c s a h' G, s.here = .att a → h.𝔇.decT c (π, behind s a h' G) = h.𝔇.decT c (π, s) :=
  fun π c s a h' G _ => P5J.At.noRec_decT o Zp Np cF (P5J.At.EAt Z) h.plan.shape c π (behind s a h' G) s

theorem smpq_all : ∀ π s a h' G, s.here = .att a → h.𝔇.smp (π, behind s a h' G) = h.𝔇.smp (π, s) :=
  fun π s a h' G _ => smpq_named (P5J.At.cs Zp) (P5J.At.seats Zp) π s a h' G

theorem rwq_all : ∀ π s a h' G, s.here = .att a → (d13 h.𝔇).rw (π, behind s a h' G) = (d13 h.𝔇).rw (π, s) :=
  fun π s a h' G _ => rwq_any h.𝔇 π s a h' G

theorem smpIs_all (x₁ : Look.Place) : ∀ (π : ProofFile.InstPub) (s : S) i,
    smpRAll h x₁ (s.st.oracles, s.book) i = h.𝔇.smp (π, s) ⟨sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link, seatAll h x₁⟩ i :=
  fun π s i => smpIs_named (P5J.At.cs Zp) (P5J.At.seats Zp) _ (seatAll h x₁) π s i

theorem constrIsPlus_all (Ld : Laid) (Ms : List OracleShape) : ∀ n p a₁ y w, (mgPlusAll h Ld Ms).constr n p a₁ y w ↔
    if p = .lookDigits then h.𝔇.digitsPart n a₁ y w
    else (p = .small → h.𝔇.H.base n w) ∧
      ∀ M i, h.𝔇.decT y.cell a₁ = some M → VerifiableInference.OnPublicFiles.Flat.Holds M i → bodyAll h.𝔇 n p i a₁ y w :=
  constrIs_all h

theorem bodySmall_all (h4 : (P5J.At.X Zp).p4 = true) (g : ℕ) : ∀ i a₁ a₂ y y' w,
    bodyAll h.𝔇 (2 * g + 1) .small i a₁ y w → bodyAll h.𝔇 (2 * g + 1) .small i a₂ y' w :=
  bodySmall_any h.𝔇 (notHead_any h4 g)

/-- The letter digitsPart reads neither the state nor the strings. -/
theorem digits_all (n : ℕ) (a a' : ProofFile.InstPub × S) (y y' : Strs) (w) : h.𝔇.digitsPart n a y w = h.𝔇.digitsPart n a' y' w :=
  digits_blind (P5J.At.X Zp) _ _ n a a' y y' w

/-- The body of a constraint rides over the kind's lay, whatever the strings. -/
theorem body_all (n : ℕ) (p : First.Part) (i : IdxQ) (π : ProofFile.InstPub) (s : S) (a : AttOwn) (h' : _) (G : Fork) (y y' : Strs) (w) :
    bodyAll h.𝔇 n p i (π, behind s a h' G) y' w = bodyAll h.𝔇 n p i (π, s) y w :=
  bodyAll_blind h.𝔇 (a := (π, s)) (b := (π, behind s a h' G)) rfl
    (fun p i y y' w => Kinds.Head.Law.Came.headPartK6_blind _ _ _ _ _ _ _ _ _ _ _ _ p i (π, s) (π, behind s a h' G) y y' w rfl
      (fun _ => tokH_behind π s a h' G)) n p i y y' w

theorem smpBySeat_all : SmpBySeat h.𝔇.sent.codes h.𝔇.smp := smpNamed_bySeat (P5J.At.cs Zp) (P5J.At.seats Zp)

/-- **THE CHECK: the sixteen, laid over a member.** -/
theorem rest_make {Fr : Frame} {Ld : Laid} {Ms : List OracleShape} {bs g : ℕ} {before : List (ℕ × ℕ)} {a : Attention.Plan} {x₁ : Look.Place}
    {pl : VerifiableInference.Desc.Place} {O : List Item} {Q : List Pub} {Lk : Link S Claim} {same : S → S → Bool} {blk : Block S Claim}
    {nm : String} {Zof : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Zs} (h4 : (P5J.At.X Zp).p4 = true)
    (hQ : ∀ q ∈ Q, q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨ q = .more (some (2 * g + 1)) "ledger.treesAre" ∨
      q = .more (some (2 * g + 1)) "K5.lookLeft")
    (R : K5RestAll (Fr := Fr) h Ld Ms bs g before a x₁ pl O Q Lk same blk nm Zof) :
    K5RestAll (Fr := Fr) h Ld Ms bs g before a x₁ pl O Q Lk same blk nm Zof :=
  { R with
    baseP := baseP_all g Q hQ
    baseIn := baseIn_all
    baseMakes := baseMakes_all _ _
    decTq := decTq_all h
    smpq := smpq_all h
    rwq := rwq_all h
    smpIs := smpIs_all h x₁
    constrIs := constrIsPlus_all h Ld Ms
    bodySmall := bodySmall_all h h4 g
    digitsBack := fun _ n _ _ _ _ _ _ _ _ w _ _ _ _ _ hd' => (digits_all h n _ _ _ _ w).mp hd'
    bodyBack := fun π n p _ i s att hd G _ _ _ w _ _ _ _ _ hb => (body_all h n p i π s att hd G _ _ w).mp hb
    smpBySeat := smpBySeat_all h
    runsIs := runsIs_all h
    mHIs := mHIs_all h
    rdIs := rdIs_all h
    clForm := clForm_lot }

end

end H2K5.Door

#print axioms H2K5.Door.bodyAll_blind
#print axioms H2K5.Door.rwq_any
#print axioms H2K5.Door.notHead_any
#print axioms H2K5.Door.baseP_all
#print axioms H2K5.Door.baseIn_all
#print axioms H2K5.Door.baseMakes_all
#print axioms H2K5.Door.decTq_all
#print axioms H2K5.Door.smpq_all
#print axioms H2K5.Door.rwq_all
#print axioms H2K5.Door.smpIs_all
#print axioms H2K5.Door.constrIsPlus_all
#print axioms H2K5.Door.bodySmall_all
#print axioms H2K5.Door.digits_all
#print axioms H2K5.Door.body_all
#print axioms H2K5.Door.smpBySeat_all
#print axioms H2K5.Door.rest_make
