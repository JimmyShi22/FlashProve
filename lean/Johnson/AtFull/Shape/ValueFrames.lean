-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ValueFrames.lean: FIFTY MEMBERS WITHOUT A ROUND OF THE PROOF FILE's OWN FIRST
CHAIN WHOSE "RETURNS" ASKS A NAMED TEST, IN THE FRAME's OWN FORM: the two premises that the rule for
acceptance asks at a member: Carries and Returns
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the reader shA of
Johnson/AtFull/Shape/FrameForm.lean (the chain's shape and the rows' makes): "behind the batching"
(25) and K9's "the one equation" (25). A joining of laws; nothing is evaluated.

  `st_putTl`, `st_k8set`, `bareRun_st`, `freeRunH_st`: the runs behind the batching leave the
    statement.
  `behind_st`, `behind₃_st`: so the whole sub-protocol does, at either order of runs.
  **`behind_frame`** (13: the attention links and the head's) · **`layers_frame`** (12): every
    letter tied as in behind_named | layers_named (SeatsNamed.lean): for every ft, every table of
    steps G with G ‹number› = liftQ (behindG (gTw w) nU | behindG₃ (gTw w) freeG nU) and every table
    vals with vals ‹number› s rs gs = behindV w nU s | behindV₃ w hp nU s (ValsBool.lean): Carries
    and Returns.
  **`oneA`**: "the one equation" ON ShA: oneGS on the shape; eqFormsU (DoorMkAtS.lean) on the makes.
  **`equation_frame`** (25): G ‹number› = oneA; vals ‹number› s rs gs = oneV s: Carries and Returns.

Limits. TWO PREMISES OF THE RULE AT 50 OF 358 MEMBERS. G and vals are letters: no table is laid. No
frame here says that a member stands at its number. behind_frame and layers_frame speak at (F0T
…).first.blocksInOrder and batchAt … + 1, equation_frame at cF.blocksInOrder and 14 l + …: Numbers.lean brings the two
spellings together. THAT A NAMED TEST ACCEPTS AT A STATE OF A RUN IS NOT SHOWN. oneV is not a test
on values alone: four of its clauses are tests on sizes that the shape does not hold yet. UNDER THE
HEAD: that it has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
(`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of
public files, in a side library. At the earlier hash. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.QuietFrames
import Johnson.AtFull.Shape.ValsBool
import Johnson.Desc.First.Batch.Shape.DoorMkAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim seatSame roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere oneEquation atS)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T fullLinks)
open ProofFile.Honest (Carries Returns)

/-! ## 1 The runs behind the batching leave the statement -/

theorem st_putTl (s : S) (tl : HTailF2) : (s.putTl tl).st = s.st := by
  unfold S.putTl
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem st_k8set (s : S) (q : K8Part) : (k8PartP.set s q).st = s.st := by
  have e : k8PartP.set s q = (s.putTl q.tl).putFork q.F := rfl
  rw [e, putFork_st, st_putTl]

theorem bareRun_st {f : K8Part → Except String K8Part} {s t : S} (h : bareRun f s = .ok t) :
    t.st = s.st := by
  unfold bareRun VerifiableInference.Desc.First.K8.atRecord at h
  cases hq : k8PartP.get? s with
  | none => rw [hq] at h; exact nomatch h
  | some q =>
    rw [hq] at h
    dsimp only at h
    cases hf : f q with
    | error e => rw [hf] at h; exact nomatch h
    | ok y =>
      rw [hf] at h
      obtain rfl : k8PartP.set s y = t := Except.ok.inj h
      exact st_k8set s y

theorem freeRunH_st {hp : Layer.HPlan2} {s t : S} (h : freeRunH hp s = .ok t) : t.st = s.st := by
  unfold freeRunH at h
  cases hq : VerifiableInference.Desc.named "the part is not there"
      (OnBytes.Desc.First.K4.part? s) with
  | error e => rw [hq] at h; exact nomatch h
  | ok q =>
    rw [hq] at h
    cases hf : OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn hp q with
    | error e =>
      have h' : ((Except.error e : Except String OnBytes.Desc.First.K4.Part).map
        (OnBytes.Desc.First.K4.setPart s)) = .ok t := by
        rw [← hf]
        exact h
      exact nomatch h'
    | ok y =>
      have h' : ((Except.ok y : Except String OnBytes.Desc.First.K4.Part).map
        (OnBytes.Desc.First.K4.setPart s)) = .ok t := by
        rw [← hf]
        exact h
      obtain rfl : OnBytes.Desc.First.K4.setPart s y = t := Except.ok.inj h'
      rfl

theorem behind_st {L : Link S Claim} {i : Nat} {p : VerifiableInference.Desc.First.K8.ParW}
    {name : String} {a : Place}
    (ho : L.orderAfter = [(i, "K8.lsTail"), (i, "K8.tests")])
    (h : L.hear[i]? = some (IM.seatedAs ProofFile.sameReply
      (VerifiableInference.Desc.First.K8.whole p) name a)) {s t : S}
    (hr : L.runBehind s = .ok t) : t.st = s.st := by
  have K := k8Runs_seated h
  obtain ⟨-, s₁, a₁, a₂⟩ := (runBehind_two ho K.look₁ K.look₂ s t).1 hr
  rw [bareRun_st ((bind_seatSame_iff _ _ s₁ t).1 a₂).1,
    bareRun_st ((bind_seatSame_iff _ _ s s₁).1 a₁).1]

theorem behind₃_st {L : Link S Claim} {i : Nat} {p : VerifiableInference.Desc.First.K8.ParW}
    {name : String} {a : Place} {hp : Layer.HPlan2}
    (ho : L.orderAfter = [(i, "K8.lsTail"), (2, "free-slot"), (i, "K8.tests")])
    (h : L.hear[i]? = some (IM.seatedAs ProofFile.sameReply
      (VerifiableInference.Desc.First.K8.whole p) name a))
    (hF : ((L.hear[2]?).bind fun b => b.after.lookup "free-slot") =
      some fun t => (freeRunH hp t).bind (seatSame ProofFile.sameReply t)) {s t : S}
    (hr : L.runBehind s = .ok t) : t.st = s.st := by
  have K := k8Runs_seated h
  obtain ⟨-, s₁, s₂, a₁, a₂, a₃⟩ := (runBehind_three ho K.look₁ hF K.look₂ s t).1 hr
  rw [bareRun_st ((bind_seatSame_iff _ _ s₂ t).1 a₃).1,
    freeRunH_st ((bind_seatSame_iff _ _ s₁ s₂).1 a₂).1,
    bareRun_st ((bind_seatSame_iff _ _ s s₁).1 a₁).1]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 2 "Behind the batching" -/

theorem behind_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : Nat) (hm : m < 25)
    (hs : subAt m ≠ .layers) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (w : SegSort × Nat × TWhere),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ Bs.G₀.built[m]? = some Xl ∧
      testsWhere Zp.p.X m 0 = some w ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (batchAt fullLinks P5J.At.ps m + 1) =
          liftQ (behindG (gTw w) (ProofFile.k8ParW Zp Bs.G₀ Xl m).nU) →
        (∀ s rs gs, vals (batchAt fullLinks P5J.At.ps m + 1) s rs gs =
          behindV w (ProofFile.k8ParW Zp Bs.G₀ Xl m).nU s) →
        Carries (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ft (firstZA G vals)
            (batchAt fullLinks P5J.At.ps m + 1) ∧
          Returns (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ft (firstZA G vals)
            (batchAt fullLinks P5J.At.ps m + 1) := by
  obtain ⟨Bs, Xl, w, L, name, a, hB, hX, hw, hl, -, hflat, ho, hh⟩ := link_named h m hm
  obtain ⟨Bs₁, Xl₁, w₁, L₁, b1, b2, b3, b4, -, hc, -⟩ := behind_named h m hm hs
  obtain ⟨Bs₂, Xl₂, w₂, L₂, c1, c2, c3, c4, -, hr⟩ := behind_bool h m hm hs
  obtain rfl : Bs = Bs₁ := Except.ok.inj (hB.symm.trans b1)
  obtain rfl : Bs = Bs₂ := Except.ok.inj (hB.symm.trans c1)
  obtain rfl : Xl = Xl₁ := Option.some.inj (hX.symm.trans b2)
  obtain rfl : Xl = Xl₂ := Option.some.inj (hX.symm.trans c2)
  obtain rfl : w = w₁ := Option.some.inj (hw.symm.trans b3)
  obtain rfl : w = w₂ := Option.some.inj (hw.symm.trans c3)
  obtain rfl : L = L₁ := Option.some.inj (hl.symm.trans b4)
  obtain rfl : L = L₂ := Option.some.inj (hl.symm.trans c4)
  have ho' : L.orderAfter = [(k8No (subAt m), "K8.lsTail"), (k8No (subAt m), "K8.tests")] := by
    rw [ho]
    cases hq : subAt m with
    | layers => exact absurd hq hs
    | attention => rfl
    | head => rfl
  refine ⟨Bs, Xl, w, hB, hX, hw, fun ft G vals hG hv =>
    frame_of_value hflat (fun s rs gs t u hd hg => hc s t u hd hg)
      (fun s rs gs u hg hvv => hr s u hg hvv)
      (fun s rs gs t hd => by rw [behind_st ho' hh hd]) ft G vals hG hv⟩

theorem layers_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (hp : Layer.HPlan2) (w : SegSort × Nat × TWhere),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[2 * g]? = some Xl ∧ Bs.G₀.W.G[g]? = some hp ∧
      testsWhere Zp.p.X (2 * g) 0 = some w ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (batchAt fullLinks P5J.At.ps (2 * g) + 1) =
          liftQ (behindG₃ (gTw w) freeG (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)).nU) →
        (∀ s rs gs, vals (batchAt fullLinks P5J.At.ps (2 * g) + 1) s rs gs =
          behindV₃ w hp (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)).nU s) →
        Carries (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ft (firstZA G vals)
            (batchAt fullLinks P5J.At.ps (2 * g) + 1) ∧
          Returns (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ft (firstZA G vals)
            (batchAt fullLinks P5J.At.ps (2 * g) + 1) := by
  obtain ⟨Bs, Xl, w, L, n₈, a₈, hB, hX, hw, hl, -, hflat, ho, h8⟩ :=
    link_named h (2 * g) (by omega)
  rw [sub_even g hg] at ho h8
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  obtain ⟨Lk, b, y, e1, e2, -, hla, -, -, -, hG', -⟩ := IM.k4_of h.scope h.reads O g hg
  obtain rfl : Lk = L := Option.some.inj (e1.symm.trans hl)
  have h4 : Lk.hear[2]? = some (IM.seatedAs ProofFile.sameReply (ProofFile.k4Block y) b.name (IM.k4Place g)) :=
    e2.trans (congrArg some hla)
  have hF := free_seated h4
  obtain ⟨Bs₁, Xl₁, hp₁, w₁, L₁, b1, b2, b3, b4, b5, -, hc, -⟩ := layers_named h g hg
  obtain ⟨Bs₂, Xl₂, hp₂, w₂, L₂, c1, c2, c3, c4, c5, -, hr⟩ := layers_bool h g hg
  obtain rfl : Bs = Bs₁ := Except.ok.inj (hB.symm.trans b1)
  obtain rfl : Bs = Bs₂ := Except.ok.inj (hB.symm.trans c1)
  obtain rfl : Xl = Xl₁ := Option.some.inj (hX.symm.trans b2)
  obtain rfl : Xl = Xl₂ := Option.some.inj (hX.symm.trans c2)
  obtain rfl : y.2.hp = hp₁ := Option.some.inj (hG'.symm.trans b3)
  obtain rfl : y.2.hp = hp₂ := Option.some.inj (hG'.symm.trans c3)
  obtain rfl : w = w₁ := Option.some.inj (hw.symm.trans b4)
  obtain rfl : w = w₂ := Option.some.inj (hw.symm.trans c4)
  obtain rfl : Lk = L₁ := Option.some.inj (hl.symm.trans b5)
  obtain rfl : Lk = L₂ := Option.some.inj (hl.symm.trans c5)
  refine ⟨Bs, Xl, y.2.hp, w, hB, hX, hG', hw, fun ft G vals hG hv =>
    frame_of_value hflat (fun s rs gs t u hd hgg => hc s t u hd hgg)
      (fun s rs gs u hgg hvv => hr s u hgg hvv)
      (fun s rs gs t hd => by rw [behind₃_st (hp := y.2.hp) ho h8 hF hd]) ft G vals hG hv⟩

/-! ## 3 "The one equation" -/

/-- **"The one equation" ON ShA.** -/
def oneA (x : ShA) : Except String ShA :=
  (oneGS x.1).bind fun u =>
    match eqFormsU x.1 x.2 with
    | some F => .ok (u, F)
    | none => .error "the one equation: the row's make cannot be said"

theorem equation_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (L : Link S ProofFile.Cl), cF.links[l]? = some L ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + L.hear.length + 4 + 0) = oneA →
        (∀ s rs gs, vals (14 * l + L.hear.length + 4 + 0) s rs gs = oneV s) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 4 + 0) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 4 + 0) := by
  obtain ⟨L, b, p, eL, eb, hy⟩ := equation_at h l hl
  obtain ⟨L₁, b₁, a1, a2, hc, -⟩ := equation_step_at h l hl
  obtain ⟨L₂, b₂, c1, c2, hr⟩ := equation_bool h l hl
  obtain rfl : L = L₁ := Option.some.inj (eL.symm.trans a1)
  obtain rfl : L = L₂ := Option.some.inj (eL.symm.trans c1)
  obtain rfl : b = b₁ := Option.some.inj (eb.symm.trans a2)
  obtain rfl : b = b₂ := Option.some.inj (eb.symm.trans c2)
  refine ⟨L, eL, fun ft G vals hG hv => ⟨?_, ?_⟩⟩
  · refine carries_of_seat eb fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    unfold oneA at hu
    cases hg : oneGS (shA s).1 with
    | error e => rw [hg] at hu; exact nomatch hu
    | ok v =>
      rw [hg] at hu
      have hf : eqFormsU (shA s).1 (shA s).2 = some (formsOf t.st) :=
        one_forms p s t _ gs ((hy s t _ gs).1 hd).1
      have hu' : (match eqFormsU (shA s).1 (shA s).2 with
        | some F => (.ok (v, F) : Except String ShA)
        | none => .error "the one equation: the row's make cannot be said") = .ok u := hu
      rw [hf] at hu'
      obtain rfl := Except.ok.inj hu'
      obtain rfl := hc s _ gs t v hd hg
      rfl
  · refine returns_of_seat eb fun s rs gs u _ hu hvv => ?_
    rw [hG] at hu
    rw [hv] at hvv
    unfold oneA at hu
    cases hg : oneGS (shA s).1 with
    | error e => rw [hg] at hu; exact nomatch hu
    | ok v => exact hr s _ gs v hg hvv

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.behind_st
#print axioms Johnson.AtFull.Shape.behind₃_st
#print axioms Johnson.AtFull.Shape.behind_frame
#print axioms Johnson.AtFull.Shape.layers_frame
#print axioms Johnson.AtFull.Shape.equation_frame
#print axioms Johnson.AtFull.Shape.st_putTl
#print axioms Johnson.AtFull.Shape.st_k8set
#print axioms Johnson.AtFull.Shape.bareRun_st
#print axioms Johnson.AtFull.Shape.freeRunH_st
#print axioms Johnson.AtFull.Shape.oneA
