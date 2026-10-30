-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SitsDoor.lean (over SitsStep.lean, Johnson/Top/H0/K2Caller/DoorKeeps.lean
and Johnson/Top/H0/Walk/FrameOpened.lean): THE ROW «K02_sits»: EVERY WAY OUT OF THE SWITCH's SEATS
KEEPS WHAT THE KIND's LAW READS; AND THE SEATED BLOCKS' TESTS ON THE PLAN ARE PAID BY THE FILE's.
NO BLOCK IMPORTS THIS FILE. KeepsOut leave (K2Caller/DoorKeeps.lean): every yes of the way out
hands on a record with the same tables (codes; number of messages; each message's shape and stored
sample rows) and, group by group, the same open rows as the record that the kind's block made:
which is all that the law reads of that record.
  noMark_same · seatSame_same · guards_same   the seat's guards hand back what they are handed
  out_guards      the way out «the guards» (a place alone in a link)
  out_head        "H.1.quiet", then the guards (the head's link)
  out_finish      "F.0.quiet", then the guards (the finish)
  leaveOpened_is  a yes of leaveOpened f s t: f.opened t = .ok s'
  out_opened      leaveOpened f, f a row of framesOf (a link's first place): by «opened leaves the
                  statement» at every row (opened_keeps)
  out_head_opened "H.1.quiet", then leaveOpened f
  SitsKeeps · KeepsAt · KeepsJoined   Sits with a way out that keeps; SitsAt's and SitsJoined's
                                      arms so
  sitsAt_keeps · sitsJoined_keeps     from SitsAt | SitsJoined
  flat_planOk · back_planOk   F.planOk = true gives the test on the plan of every block of the
                              first chain's flat list, and of every block behind the links (by
                              Keeps.planOk_blocks, Johnson/Desc/PlanPasses.lean)

  k02_sits_file   k02_sits_step's sentence UNDER THE FILE's TEST ON THE PLAN, with no premise on a
                  block left, and each way out with KeepsOut
LIMITS. The way in is not spoken of (the identity but at the finish; there: K2C/FinFront.lean).
One direction. Those of Johnson/P1K2R/SitsStep.lean. No soundness is claimed.
-/
import Johnson.P1K2R.SitsStep
import Johnson.Top.H0.K2Caller.DoorKeeps
import Johnson.Top.H0.Walk.FrameOpened
import Johnson.Desc.PlanPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName seatSame)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (codeSwitchKind headOpenQ finishFrontQ finishBehindQ)
open VerifiableInference.Desc.First.K2Caller (Kept KeepsOut keepsOut_same headOpenQ_kept
  finishBehindQ_kept kept_of_st)
open H2K.JointK (Sits)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open ProofFile (Cl)
open IM (k2P Open)

theorem noMark_same {t u : S} (h : noMark t = .ok u) : u = t := by
  unfold noMark at h
  split at h
  · exact (Except.ok.inj h).symm
  · cases h

theorem seatSame_same {same : S → S → Bool} {s t u : S} (h : seatSame same s t = .ok u) :
    u = t := by
  unfold seatSame at h
  split at h
  · exact (Except.ok.inj h).symm
  · cases h

theorem guards_same {s t u : S} (h : guards s t = .ok u) : u = t := by
  unfold guards at h
  obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  rw [seatSame_same h2, noMark_same h1]

theorem out_guards : KeepsOut fun s t => guards s t :=
  keepsOut_same fun _ _ _ e => guards_same e

theorem out_head (HP : VerifiableInference.Desc.First.K2.HeadPar) :
    KeepsOut fun s t => (headOpenQ HP t).bind (guards s) :=
  KeepsOut.then (fun _ _ e => headOpenQ_kept e) out_guards

theorem out_finish : KeepsOut fun s t => (finishBehindQ t).bind (guards s) :=
  KeepsOut.then (fun _ _ e => finishBehindQ_kept e) out_guards

theorem leaveOpened_is {f : LinkFrame} {s t s' : S} (h : leaveOpened f s t = .ok s') :
    f.opened t = .ok s' := by
  unfold leaveOpened at h
  obtain ⟨m, h1, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u, h2, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u₁, h3, h⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨u₂, h4, h5⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  rw [seatSame_same h5, seatSame_same h4, noMark_same h3, ← noMark_same h1]
  exact h2

theorem out_opened {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}
    (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f) :
    KeepsOut fun s t => leaveOpened f s t := fun _ _ _ e =>
  kept_of_st (Johnson.Desc.First.Walk.Tied.opened_keeps h hf (leaveOpened_is e)).1

theorem out_head_opened {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}
    (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f)
    (HP : VerifiableInference.Desc.First.K2.HeadPar) :
    KeepsOut fun s t => (headOpenQ HP t).bind (leaveOpened f s) :=
  KeepsOut.then (fun _ _ e => headOpenQ_kept e) (out_opened h hf)

/-! ## Each arm with its way out -/

/-- Sits, with a way out that keeps what the law reads. -/
def SitsKeeps (b : Block S Cl) (p : VerifiableInference.Desc.First.K2.P2)
    (enter : S → Except String S) (leave : S → S → Except String S) : Prop :=
  Sits b (codeSwitchKind p : Block S Unit) enter leave ∧ KeepsOut leave

/-- SitsAt's three arms, each with KeepsOut. -/
def KeepsAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (b : Block S Cl) : Prop :=
  ∃ P n, prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    ((a.link = none ∧ SitsKeeps b (k2P Z a nm .finish n) finishFrontQ
        (fun s t => (finishBehindQ t).bind (guards s))) ∨
      (∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        SitsKeeps b (k2P Z a nm .head n) (fun s => .ok s)
          (fun s t => (headOpenQ HP t).bind (guards s))) ∨
      (∃ l, a.link = some l ∧ SitsKeeps b (k2P Z a nm .link n) (fun s => .ok s)
        (fun s t => guards s t)))

theorem sitsAt_keeps {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {b : Block S Cl}
    (h : SitsAt Z G a nm b) : KeepsAt Z G a nm b := by
  obtain ⟨P, n, hP, hn, h⟩ := h
  refine ⟨P, n, hP, hn, ?_⟩
  rcases h with ⟨ha, hX⟩ | ⟨l, HP, ha, hH, hX⟩ | ⟨l, ha, hX⟩
  · exact Or.inl ⟨ha, hX, out_finish⟩
  · exact Or.inr (Or.inl ⟨l, HP, ha, hH, hX, out_head HP⟩)
  · exact Or.inr (Or.inr ⟨l, ha, hX, out_guards⟩)

/-- SitsJoined's two arms, each with KeepsOut. -/
def KeepsJoined (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (b : Block S Cl)
    (f : LinkFrame) : Prop :=
  ∃ P n, prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    ((∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        SitsKeeps b (k2P Z a nm .head n) (fun s => .ok s)
          (fun s t => (headOpenQ HP t).bind (leaveOpened f s))) ∨
      (∃ l, a.link = some l ∧ SitsKeeps b (k2P Z a nm .link n) (fun s => .ok s)
        (fun s t => leaveOpened f s t)))

theorem sitsJoined_keeps {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String}
    {b : Block S Cl} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}
    (hfs : framesOf Z.p.built.links Z.first Z.p.X = .ok fs) (hf : fs[l]? = some f)
    (h : SitsJoined Z G a nm b f) : KeepsJoined Z G a nm b f := by
  obtain ⟨P, n, hP, hn, h⟩ := h
  refine ⟨P, n, hP, hn, ?_⟩
  rcases h with ⟨l', HP, ha, hH, hX⟩ | ⟨l', ha, hX⟩
  · exact Or.inl ⟨l', HP, ha, hH, hX, out_head_opened hfs hf HP⟩
  · exact Or.inr ⟨l', ha, hX, out_opened hfs hf⟩

/-! ## The blocks' tests on the plan, from the file's -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}

theorem flat_planOk (O : Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true) :
    ∀ b ∈ c.blocksInOrder, b.planOk = true := by
  have e := O.desc
  subst e
  exact (VerifiableInference.Desc.Keeps.planOk_blocks _ hp).1

theorem back_planOk (O : Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    {b : Block S Cl} (hb : b ∈ c.back) : b.planOk = true := by
  have h := flat_planOk O hp { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } (by
                          unfold Chain.blocksInOrder
                          exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩)))
  have h' : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := h
  rw [Bool.and_eq_true] at h'
  exact h'.1

/-- **K02_sits UNDER THE FILE's TEST ON THE PLAN: no premise on a block is left; every way out
keeps what the law reads.** -/
theorem k02_sits_file (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hp : F.planOk = true) :
    ∃ Z Bs base c A B, Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧
      (∀ l, 1 ≤ l → l < 24 → ∃ (b : Block S Cl) (nm : String) (fs : List LinkFrame)
        (f : LinkFrame), c.blocksInOrder[14 * l + 0 + 2]? = some b ∧
          framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧ fs[l]? = some f ∧
          KeepsJoined Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } nm b f) ∧
      (∃ (b : Block S Cl) (nm : String), c.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧
        KeepsAt Z Bs.G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } nm b) ∧
      (∃ (b : Block S Cl) (nm : String), c.back[0]? = some b ∧
        KeepsAt Z Bs.G₀ IM.k2PlaceF nm b) := by
  obtain ⟨Z, Bs, base, c, A, B, O, h1, h2, h3⟩ := k02_sits_step hS hR hF
  refine ⟨Z, Bs, base, c, A, B, O, fun l a1 a24 => ?_, ?_, ?_⟩
  · obtain ⟨b, nm, hf, h⟩ := h1 l a1 a24
    obtain ⟨fs, f, hfs, hff, hj⟩ := h (flat_planOk O hp b (List.mem_of_getElem? hf))
    exact ⟨b, nm, fs, f, hf, hfs, hff, sitsJoined_keeps hfs hff hj⟩
  · obtain ⟨b, nm, hf, h⟩ := h2
    exact ⟨b, nm, hf, sitsAt_keeps (h (flat_planOk O hp b (List.mem_of_getElem? hf)))⟩
  · obtain ⟨b, nm, hf, h⟩ := h3
    exact ⟨b, nm, hf, sitsAt_keeps (h (back_planOk O hp (List.mem_of_getElem? hf)))⟩

end

end P1K2

#print axioms P1K2.flat_planOk
#print axioms P1K2.back_planOk
#print axioms P1K2.k02_sits_file

#print axioms P1K2.out_guards
#print axioms P1K2.out_head
#print axioms P1K2.out_finish
#print axioms P1K2.out_opened
#print axioms P1K2.out_head_opened
