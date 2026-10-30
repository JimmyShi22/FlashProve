-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RidesAtHead.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): at the library's composed meaning (`mgAll`,
Johnson/Desc/Sound/MgAll.lean) over the head's parameters, WITH THE DECODER OF THE STORED TABLE A
CONSTANT and the carried word's sentence a letter, four fields say, of every state that `K5Keeps`
(Johnson/Desc/K5/Honest/Law/Returns.lean) ties to the state in front, what they say in front: the
parts of the segments' relations, the head's segment among them; the open segment's classes of rows;
the pile; the lookup's forms "objects". With "no mark" these are five of the six sorts of items that
ride past the block of an attention segment's own rounds; the sixth is the index masks' pin, whose
sentence on the honest side is a letter of another file.

It is Johnson/Desc/K5/Honest/Law/RidesK5.lean and ObjectsOn.lean at the head's letters. Who hands
what:
  the request is read off the public part alone: by unfolding;
  the decoder: the constant: it reads neither a string nor a state. AT THE LIBRARY's OWN DECODER,
    WHICH READS THE STRINGS, `constr_on_head` WOULD NOT HOLD AS TYPED: there both strings are free;
  the head's part of the relation reads the state through the request and the heard token alone, and
    no string: the library's `headPartK6_blind` (Johnson/Desc/Kinds/Law/HeadCutsK6.lean);
  the reader of the pile's rows reads the statement and the book: by its text (`rwBook`,
    Johnson/Desc/K13/Law/ReaderByBook.lean);
  for "objects": the ledger's lengths and "each row's worth at every later ledger is one term of
    the mask row": the lookup's promise in front (`K3LeftOutIs`, out of `door_at_head`,
    Johnson/Desc/K5/Honest/Law/DoorAtHead.lean); "the rows name no entry": `bareLeft_head`
    (Johnson/Desc/K5/Honest/Law/BehindAtHead.lean); the readers' answers AT EVERY STATE with a
    ledger and what the lookup left: the library's `objIs_gstIs_all`
    (Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean); the stated function leaves the mask row AT
    EVERY STATE: by its make.

Main names: `tok_keeps`, `constr_on_head`, `row_on_head`, `pile_on_head`, `objects_on_head`.

Limits. The head is a hypothesis. That a state of an honest run is reached, bears no mark and meets
the promise in front is not shown here. At the function `OnBytes.secondHashFunction`, of which nothing is asked
here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RidesK5
import Johnson.Desc.K5.Honest.Law.ObjectsOn
import Johnson.Desc.K5.Honest.Law.BehindAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (restO readsRest_field fork_front)
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)
open H2K5.Door

/-- The heard token is kept. Conditional: K. -/
theorem tok_keeps {P : Type} (π : P) {s s' : S} (K : K5Keeps s s') :
    P5J.tokHOf (π, s') = P5J.tokHOf (π, s) := by
  have e : s'.heardTok? = s.heardTok? :=
    (readsRest_field (fun t : S => t.heardTok?) fun t => by
      unfold restO
      split <;> rfl) s' s K.1
  unfold P5J.tokHOf P5J.tokOfHeard
  rw [e]

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (c : P5J.CellsM OnBytes.Flat.numsFull)
  (carryX : ℕ → ProofFile.InstPub × S → Strs → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
    Prop)

/-- **The parts of the segments' relations go on**, the head's segment among them, the digits' part
aside. Conditional: the head; hp. -/
theorem constr_on_head (n : ℕ) (p : First.Part) (hp : p ≠ .lookDigits) :
    GoesOn (relK5 ProofFile.InstPub)
      ((mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).constr n p) := by
  rintro ⟨π, s⟩ y ⟨π', s'⟩ y' w ⟨e, K⟩ hm
  obtain rfl : π = π' := e
  have h1 := (constrIs_any _ mgBase _ _ _ _ _).1 hm
  refine (constrIs_any _ mgBase _ _ _ _ _).2 ?_
  rw [if_neg hp] at h1 ⊢
  refine ⟨h1.1, fun M i hM hH => ?_⟩
  rw [bodyAll_blind _ (a := (π, s)) (b := (π, s')) rfl
    (fun p i y y' w => Kinds.Head.Law.Came.headPartK6_blind _ _ _ _ _ _ _ _ _ _ _ _ p i (π, s)
      (π, s') y y' w rfl (fun _ => tok_keeps π K)) n p i y y' w]
  exact h1.2 M i hM hH

/-- **The open segment's classes of rows go on.** Conditional: the head. -/
theorem row_on_head (m : ℕ) (cl : RowClass) :
    GoesOn (relK5 ProofFile.InstPub)
      ((mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).row m cl) :=
  row_on _ h.𝔇.N h.𝔇.arr rfl m cl

/-- **The pile goes on.** Conditional: the head. -/
theorem pile_on_head :
    GoesOn (relK5 ProofFile.InstPub)
      (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).pile :=
  pile_on _ mgBase (d13 { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX }) rfl
    (fun a b e K => by
      obtain ⟨π, s⟩ := a
      obtain ⟨π', s'⟩ := b
      have e1 : s.st = s'.st := keeps_reads VerifiableInference.Desc.First.Att.P.rest_st K
      have e2 : s.book = s'.book := keeps_reads VerifiableInference.Desc.First.Att.P.rest_book K
      show K13.Law.rwBook h.𝔇.arr h.𝔇.mat13 (π, s) = K13.Law.rwBook h.𝔇.arr h.𝔇.mat13 (π', s')
      unfold K13.Law.rwBook
      show (fun w => _) = fun w => _
      simp only [e1, e2])

/-- **The lookup's forms "objects" go on**, from a state that is reached at the border in front of
the block, bears no mark and meets the promise there, to every state that `K5Keeps` ties to it; at
any strings. Conditional: the head; as `door_at_head`, with hr at 14 (2 g + 1) + 4; K; hm: the
item's sentence in front. -/
theorem objects_on_head {L : Laid} (hL : P5J.At.laid? Zp = some L) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} {x₁ : Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {W' : Type}
    (Mg : Meaning ProofFile.InstPub W') (hpub : Mg.pub = (mgAtAll h).pub)
    (hpubP : Mg.pubP = (mgAtAll h).pubP) (O : List Item) (Q : List Pub)
    (Oq : Open8 (2 * g + 1) Q) {π : ProofFile.InstPub} {s s' : S} {y₀ : Strs}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4) (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) Mg P5J.At.links (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s)
      y₀)
    (K : K5Keeps s s') (y y' : Strs) (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hm : (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).formsT (2 * g + 1) 2
      "objects" (π, s) y w) :
    (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).formsT (2 * g + 1) 2
      "objects" (π, s') y' w := by
  obtain ⟨_, att, att', e, e', _, _⟩ := id K
  obtain ⟨_, gL, Y, hLf⟩ := door_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon
    (id : Aff → Aff) (fun _ => (none : Option Unit))
  obtain ⟨F, F', rs₀, _, _, Lq, e1, e2, _⟩ := hLf
  obtain rfl : F' = att.F :=
    Option.some.inj ((show s.fork? = some F' from e2).symm.trans (fork_front e))
  obtain ⟨g₁, G₁, hlk, hbr, _, _⟩ := bareLeft_head h hg hr
  obtain rfl : g₁ = gL := Option.some.inj (hlk.symm.trans Y.heard)
  obtain ⟨Lk, hLk⟩ := lkAt_all h hg
  obtain ⟨hObj, hGst⟩ := objIs_gstIs_all h hg hLk
  have hlk' : s'.lookHeard? = some g₁ := by
    have hq := keeps_att K e e'
    unfold S.lookHeard? at hlk ⊢
    rw [e] at hlk
    rw [e']
    have hq' : att'.lookHeard = att.lookHeard := congrArg (·.lookHeard) hq
    simpa [hq'] using hlk
  have rO := runsO_plus h.𝔇.pubD g h.𝔇.links (runsIs_all h) (sub_full hg)
  have hm' : (∀ p ∈ h.𝔇.pubD.runs (2 * g + 1) 2 "objects",
      formsTQ (h.𝔇.pubD.Rd (2 * g + 1)) h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) p.1 p.2 s
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms w)) ∧ ("objects" = "weights" → _) := hm
  refine (show (∀ p ∈ h.𝔇.pubD.runs (2 * g + 1) 2 "objects",
      formsTQ (h.𝔇.pubD.Rd (2 * g + 1)) h.𝔇.St (h.𝔇.pubD.N.sent (2 * g + 1) 0) p.1 p.2 s'
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms w)) ∧ ("objects" = "weights" → _) from
    ⟨fun p hp => ?_, fun hw => absurd hw (by decide)⟩)
  have h0 := hm'.1 (1, "objects") (by rw [rO]; simp)
  rw [rO] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact formsTQ_objects_on _ _ _ K e
      ⟨Lq.padLeft.fit.1, Lq.padLeft.fit.2.1, Lq.padLeft.fit.2.2⟩
      (fun i hi => ⟨_, Lq.heardIs.rows i hi⟩) (hObj s att.F _ (fork_front e) hlk hbr)
      (hObj s' att'.F _ (fork_front e') hlk' hbr) (fun _ => rfl) (fun _ => rfl) _ h0
  · exact formsTQ_guests_on _ _ _ e' (hGst s' att'.F (fork_front e')) _

end

end H2K5.Honest

#print axioms H2K5.Honest.tok_keeps
#print axioms H2K5.Honest.constr_on_head
#print axioms H2K5.Honest.row_on_head
#print axioms H2K5.Honest.pile_on_head
#print axioms H2K5.Honest.objects_on_head
