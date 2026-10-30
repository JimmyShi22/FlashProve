--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/WideToRun.lean: THE SMALLNESS TEST: THE TWO HALVES OF
"THE RUN OF EQUATIONS IS CALLED AT WHAT STOOD AT THE DRAW" JOINED, AT ALL 25 LINKS OF THE
DESCRIPTION'S FIRST CHAIN. NO SOUNDNESS.

The law of the draw speaks of the smallness test's part of the verifier's state at the draw's entry.
The kind's run of claims "K8.equations" is called later, inside the link's batching. TWO HALVES LIE:
  ours (WideAtSeat.lean): over the draw's entry and the entries between it and the batching's
    the reading `wide` stays (sizes, arrays, the closed list of tables), and over the entries behind
    the draw's the reading `wideM` (the same with the drawn matrix);
  another thread's (`k08_front_scope`): a yes of the link's batching from a
    state sIn calls `equations` at a part q with sIn.tl? = some q.tl, sIn.funs? = some q.funs and
    q.funs = q.tl.funs.
Here they meet:
  `wide_stays`, `wideM_stays`: our half at an opening's own letters.
  `RunAtDraw c Lk x sIn sB`: the other thread's own sentence `FrontSays`, WHOLE (so the part q is
    the part of the state at which the run was called, and the number of the first claim is the
    run's own); and, at the value tl that sIn holds (FrontSays: it is q.tl): every state from which
    the fold over the draw's entry and the entries between hands sIn on has `wide` = that of tl;
    every state from which the fold over the entries between hands sIn on has `wideM` = that of tl.
  `wide_to_run`: at each of the 25 stretches: the entry behind the stretch is the link's batching's;
    and every yes of it from sIn to sB gives `RunAtDraw`.
  `run_along_fold`: THE SEAM TO THE FOLD: where one fold, from any state, goes over the entries up
    to and with the batching's: the states u₀ in front of the draw's entry, u₁ behind it and uB in
    front of the batching's are there, `FrontSays` holds from uB's state to the state handed on, and
    `wide` of u₀'s and `wideM` of u₁'s are those of uB's value. By the landed `foldBlocks_split`
    (Johnson/Desc/FoldKeeps.lean), `List.take_add` and another thread's `fold_back`, `fold_next`.
  `k08_wide_to_run`: **`wide_to_run` from the description's return, in the goals' scope.**
SO: the equations are stated at the sizes, the arrays and the closed list of tables that stood IN
FRONT OF the draw, and at the matrix that the draw laid.
Limits. Nothing says that the blocks say yes. The part's ledger and the number of the first claim
are the run's own; nothing ties them to the draw. AT `OnBytes.secondHashFunction` ALONE: nothing at another
earlier hash.

-/
import Johnson.P1K8R.WideAtSeat
import Johnson.TocK8R.FrontAtSeat
import Johnson.IMR.FoldTools
import Johnson.Desc.FoldKeeps

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription OpenedColumn Claim foldBlocks claimsInBy)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.TailClaims (K8Part equations)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- Over the draw's entry and the entries between. -/
theorem wide_stays (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (x : ℕ × ℕ × ℕ)
    (hx : x ∈ stretches) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (H : foldBlocks ft ((c.blocksInOrder.drop (14 * x.1 + x.2.1 + 2)).take (x.2.2 + 1)) s rs cols =
      .ok out) : wide out.1 = wide s := by
  refine foldLeavesWide ft _ s rs cols out (fun b hb => ?_) H
  obtain ⟨j, hj, e⟩ := mem_stretch hb
  cases j with
  | zero => exact (staysAt_open hS hR O x hx).1 b e
  | succ j =>
    exact (staysAt_open hS hR O x hx).2 j (by omega) b
      (by rw [show 14 * x.1 + x.2.1 + 3 + j = 14 * x.1 + x.2.1 + 2 + (j + 1) by omega]; exact e)
      _ wideOf keeps4_wideOf

/-- Over the entries between. -/
theorem wideM_stays (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (x : ℕ × ℕ × ℕ)
    (hx : x ∈ stretches) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (H : foldBlocks ft ((c.blocksInOrder.drop (14 * x.1 + x.2.1 + 3)).take x.2.2) s rs cols = .ok out) :
    wideM out.1 = wideM s := by
  refine VerifiableInference.Desc.foldLeaves S Cl _ wideM ft _ s rs cols out (fun b hb => ?_) H
  obtain ⟨j, hj, e⟩ := mem_stretch hb
  exact (staysAt_open hS hR O x hx).2 j hj b e _ wideMOf fun _ _ _ _ _ => rfl

/-- What a yes of the batching behind a stretch says, with what stood at the draw: the other
thread's own sentence, whole; and, at the value tl that sIn holds, the two clauses of the join. -/
def RunAtDraw (c : Chain S Cl) (Lk : Link S Cl) (x : ℕ × ℕ × ℕ) (sIn sB : S) : Prop :=
  TocK8.FrontSays Lk (TocK8.ixOf (IM.subAt x.1)) (TocK8.preOf (IM.subAt x.1))
    (TocK8.postOf (IM.subAt x.1)) sIn sB ∧
  ∀ tl, sIn.tl? = some tl →
    (∀ (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (R' : List Fmt.RoundView) (C' : List OpenedColumn),
      foldBlocks ft ((c.blocksInOrder.drop (14 * x.1 + x.2.1 + 2)).take (x.2.2 + 1)) s rs cols =
        .ok (sIn, R', C') → wide s = some (wideOf tl)) ∧
    ∀ (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (R' : List Fmt.RoundView) (C' : List OpenedColumn),
      foldBlocks ft ((c.blocksInOrder.drop (14 * x.1 + x.2.1 + 3)).take x.2.2) s rs cols =
        .ok (sIn, R', C') → wideM s = some (wideMOf tl)

/-- **The two halves at one part.** -/
theorem wide_to_run (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ x ∈ stretches, ∃ Lk : Link S Cl, c.links[x.1]? = some Lk ∧
      c.blocksInOrder[14 * x.1 + x.2.1 + 3 + x.2.2]? =
        some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      ∀ (sIn sB : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
        (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide sIn rs gs = .ok sB →
        RunAtDraw c Lk x sIn sB := by
  intro x hx
  obtain ⟨Lk, e, hf⟩ := batch_behind hS hR O x hx
  have hl : x.1 < 25 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.1 hl
  obtain ⟨Lk', e', hT⟩ := TocK8.k08_front_scope hS hR O x.1 hl
  obtain rfl : Lk' = Lk := Option.some.inj (e'.symm.trans e)
  refine ⟨Lk', e, hf, fun sIn sB rs gs h => ?_⟩
  refine ⟨hT sIn sB rs gs h, fun tl ht => ⟨fun ft s rs' cols R' C' H => ?_,
    fun ft s rs' cols R' C' H => ?_⟩⟩
  · rw [← wide_stays hS hR O x hx ft s rs' cols _ H]
    show sIn.tl?.map wideOf = _
    rw [ht]
    rfl
  · rw [← wideM_stays hS hR O x hx ft s rs' cols _ H]
    show sIn.tl?.map wideMOf = _
    rw [ht]
    rfl

/-- **ALONG ONE FOLD**: from any state, over the entries up to and with the batching's. -/
theorem run_along_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (x : ℕ × ℕ × ℕ)
    (hx : x ∈ stretches) (ft : ℕ) (s₀ : S) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn)
    (f : foldBlocks ft (c.blocksInOrder.take (14 * x.1 + x.2.1 + 3 + x.2.2 + 1)) s₀ R C = .ok out) :
    ∃ (Lk : Link S Cl) (u₀ u₁ uB : S × List Fmt.RoundView × List OpenedColumn) (tl : HTailF2),
      c.links[x.1]? = some Lk ∧
      foldBlocks ft (c.blocksInOrder.take (14 * x.1 + x.2.1 + 2)) s₀ R C = .ok u₀ ∧
      foldBlocks ft (c.blocksInOrder.take (14 * x.1 + x.2.1 + 3)) s₀ R C = .ok u₁ ∧
      foldBlocks ft (c.blocksInOrder.take (14 * x.1 + x.2.1 + 3 + x.2.2)) s₀ R C = .ok uB ∧
      TocK8.FrontSays Lk (TocK8.ixOf (IM.subAt x.1)) (TocK8.preOf (IM.subAt x.1))
        (TocK8.postOf (IM.subAt x.1)) uB.1 out.1 ∧
      uB.1.tl? = some tl ∧ wide u₀.1 = some (wideOf tl) ∧ wideM u₁.1 = some (wideMOf tl) := by
  obtain ⟨Lk, e, hf, hY⟩ := wide_to_run hS hR O x hx
  obtain ⟨tE, RE, CE⟩ := out
  obtain ⟨tB, RB, CB, fB⟩ := Meaning.K2.fold_back (k := 14 * x.1 + x.2.1 + 3 + x.2.2) f
  obtain ⟨rs, gs, d⟩ := Meaning.K2.fold_next hf fB f
  obtain ⟨hFS, hJ⟩ := hY tB tE rs gs d
  obtain ⟨_, _, _, _, _, _, q, _, _, _, _, _, ht, _⟩ := hFS
  have fB0 := fB
  rw [show 14 * x.1 + x.2.1 + 3 + x.2.2 = (14 * x.1 + x.2.1 + 2) + (x.2.2 + 1) by omega,
    List.take_add] at fB0
  obtain ⟨t₀, R₀, C₀, f₀, g₀⟩ := VerifiableInference.Desc.Keeps.foldBlocks_split ft _ _ _ _ _ _ fB0
  have fB1 := fB
  rw [List.take_add] at fB1
  obtain ⟨t₁, R₁, C₁, f₁, g₁⟩ := VerifiableInference.Desc.Keeps.foldBlocks_split ft _ _ _ _ _ _ fB1
  exact ⟨Lk, (t₀, R₀, C₀), (t₁, R₁, C₁), (tB, RB, CB), q.tl, e, f₀, f₁, fB, hY tB tE rs gs d |>.1,
    ht, (hJ q.tl ht).1 ft t₀ R₀ C₀ RB CB g₀, (hJ q.tl ht).2 ft t₁ R₁ C₁ RB CB g₁⟩

end

/-- **FROM THE DESCRIPTION'S RETURN, IN THE GOALS' SCOPE.** -/
theorem k08_wide_to_run {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ x ∈ stretches, ∃ Lk : Link S Cl, c.links[x.1]? = some Lk ∧
        c.blocksInOrder[14 * x.1 + x.2.1 + 3 + x.2.2]? =
          some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
        ∀ (sIn sB : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
          (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide sIn rs gs = .ok sB →
          RunAtDraw c Lk x sIn sB := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  exact ⟨Z, Bs.G₀, c, A, B, O.pub, O.blank, O.desc, wide_to_run hS hR O⟩

end P1K8S

#print axioms P1K8S.wide_to_run
#print axioms P1K8S.run_along_fold
#print axioms P1K8S.k08_wide_to_run
