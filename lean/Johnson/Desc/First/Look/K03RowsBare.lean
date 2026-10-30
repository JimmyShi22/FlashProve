-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K03RowsBare.lean: THE KIND "LOOKUP" (K3): WHAT AN ACCEPT OF A LOOKUP LEAVES,
AT THE STATE THAT IS REACHED BEHIND IT: a fact on the verifier's state along the fold of the first
chain of the IOP as written in Lean (our files: the description) that `ProofFile.onlineDescription` returns, in the
goals' scope, AT THE 24 LINKS IN FRONT OF THE HEAD's: something is heard at the lookup's seat, and
its rows bear no entry. On the way: IN FRONT OF EACH LOOKUP THERE THE LINK's LEDGER IS OPEN, WITH
ITS SIZES. Definitions, and theorems with their proofs.

  `seatOf_reads`, `seatOf_fork`, `seatOf_putFork`, `seatOf_headClaim`: small laws on the two seats.
  **`stated_rowsBare`**: general in the maker of claims, the public data and the address: an accept
    of `K3.theStated`'s value, from a state whose ledger is open with its sizes, leaves at the seat
    that the piece tells something heard whose rows bear no entry: the lookups' `via_rowsBare`
    (Johnson/Top/H/Keep/RowsBare.lean), then their `quietAt_frame` for the step without a round.
  `SizedAt s`: a ledger is open at the state s, with its sizes.
  `foldCut`: a fold over one sub-protocol (block) more is the fold in front and that one's accept.
  `kindsBehind1`, `subAt_ne_head`: on the driver's list of kinds.
  `hear_steps`: in scope: the hearing block at index i ≥ 1 of a kind of `behindKinds` steps:
    `chain_hear_alone` (IMR/LaidFirst.lean), `alone_underR` (IMR/SeatForm.lean); the seven kinds'
    laws through `kindsStepLook` (K9x/K03Ran.lean).
  **`opened_sized`**: l < 24: behind the link's first place: `SizedAt`: `frames_sit`, `frames_arms`
    (both in Johnson/IMR/), with `OpensSized` at openLayZero, openAtt, openLay (StartsSized.lean).
  **`sized_upTo`**: l < 24: behind each of the link's seven hearing blocks: `SizedAt`.
  **`rowsBare_reached`**: l < 24, both lookups.

PREMISES: the goals' scope (hS, hR); the description's letters (O); its test on the list of rounds
(our files: the plan) accepts (hOk). THE START OF THE FOLD IS FREE.

Limits. Nothing on soundness. NOT AT THE HEAD's LINK: there the ledger is opened at K2's place;
which of the three forms that `IM.K2Is` leaves open stands there is shown by nobody. A law from an
accept: idle where the fold rejects. That a fold returns anywhere is a run's word.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K03States
import Johnson.Desc.First.Look.K03PlanOf
import Johnson.Desc.First.K9x.K03Ran
import Johnson.Desc.First.Look.K3StatedSteps
import Johnson.Top.H.Keep.RowsBare
import Johnson.IMR.FrameYes
import Johnson.Desc.First.StartsSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits pieceAt)

section
variable {Cl : Type}

theorem seatOf_reads (claim : Aff → Cl) (d : Bool) : Desc.K3.SeatReads (seatOf claim d) := by
  cases d
  · exact Desc.K3.seatCalls_reads claim
  · exact Desc.K3.seatDigits_reads claim

theorem seatOf_fork (claim : Aff → Cl) (d : Bool) (s : S) : (seatOf claim d).fork s = s.fork? := by
  cases d <;> rfl

theorem seatOf_putFork (claim : Aff → Cl) (d : Bool) (s : S) (G : Fork) :
    (seatOf claim d).heard (S.putFork s G) = (seatOf claim d).heard s := by
  cases d
  · exact lookHeard_putFork s G
  · exact congrArg (fun x : Option HTailF2 => x.bind (·.heard)) (tl_putFork s G)

theorem seatOf_headClaim (claim : Aff → Cl) (d : Bool) (s : S) (a : Desc.First.HeadOwn) (c : _)
    (ha : s.here = .head a) :
    (seatOf claim d).heard { s with here := .head { a with claim := some c } } =
      (seatOf claim d).heard s := by
  cases d
  · have k : S.lookHeard? ({ s with here := .head { a with claim := some c } } : S) =
        S.lookHeard? s := by simp [S.lookHeard?, ha]
    exact k
  · have k : tlHeard ({ s with here := .head { a with claim := some c } } : S) = tlHeard s := by
      simp [tlHeard, S.tl?, ha]
    exact k

/-- **What an accept of the stated block leaves as heard: its rows bear no entry.** -/
theorem stated_rowsBare (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (d : Bool) (hl : a.link = some i) (hpc : a.piece = pieceAt X i d) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (hdec : B.decide s rs gs = .ok t)
    {F : Fork} (hf : s.fork? = some F) (hS : Sized F) :
    ∃ g, (seatOf claim d).heard t = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨B₁, h1, -, ed, -, ep⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hw⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ h1
  obtain ⟨i', digits, p, sent, laid, hl', hpc', -, -, -, -, edb, -, hpb⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hl.symm.trans hl')
  obtain rfl : d = digits := Desc.K3.pieceAt_inj X i (hpc.symm.trans hpc')
  rw [ed] at hdec
  rw [ep] at hOk
  have e : Desc.K3.seatOfLookupOnDigitsOrCalls claim d = seatOf claim d := by
    cases d <;> simp [Desc.K3.seatOfLookupOnDigitsOrCalls, seatOf]
  have own : ∀ (s₁ : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      b.planOk = true → b.decide s rs gs = .ok s₁ →
      ∃ g, (seatOf claim d).heard s₁ = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] := by
    intro s₁ rs gs hp hdc
    rw [edb, e] at hdc
    have hv := hpb hp
    rw [e] at hv
    exact via_rowsBare _ (seatOf_reads claim d) _ _ _ _ _ s s₁ rs gs hv hdc
      ((seatOf_fork claim d s).trans hf) hS
  rcases hw with ⟨-, rfl⟩ | ⟨f, hf', rfl⟩
  · exact own t rs gs hOk hdec
  · have hp : b.planOk = true := by
      simpa [Desc.Block.andThen, Desc.roundlessBlock] using hOk
    obtain ⟨i', -, hf''⟩ := Option.bind_eq_some_iff.1 hf'
    have hdec' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
        (fun s₁ => f s₁) = .ok t := hdec
    cases hb1 : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
    | error x =>
      rw [hb1] at hdec'
      have k : (Except.error x : Except String S) = .ok t := hdec'
      cases k
    | ok s₁ =>
      rw [hb1] at hdec'
      have hq : f s₁ = .ok t := hdec'
      obtain ⟨g, hg, hbare⟩ := own s₁ _ _ hp hb1
      exact ⟨g, (quietAt_frame (seatOf claim d).heard (seatOf_putFork claim d)
        (seatOf_headClaim claim d) X i' _ f hf'' s₁ t hq).1 g hg, hbare⟩

end

/-! ## The ledger in front of a lookup has its sizes -/

/-- A ledger is open at the state, with its sizes. -/
def SizedAt (s : S) : Prop := ∃ F, s.fork? = some F ∧ Sized F

/-- A fold over one block more: the fold in front, and that block's accept. -/
theorem foldCut {Cl : Type} (L : List (Block S Cl)) (n : ℕ) (b : Block S Cl)
    (hb : L[n]? = some b) {ft : ℕ} {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : Desc.foldBlocks ft (L.take (n + 1)) s₀ R C = .ok (t, R', C')) :
    ∃ s R₁ C₁ rs gs, Desc.foldBlocks ft (L.take n) s₀ R C = .ok (s, R₁, C₁) ∧
      b.decide s rs gs = .ok t := by
  have e : L.take (n + 1) = L.take n ++ [b] := by
    rw [List.take_add_one, hb]
    rfl
  rw [e] at h
  obtain ⟨m, cols', -, Hp, Hm⟩ := Desc.foldAt S Cl (fun _ _ => True)
    ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩ ft (L.take n) [b] s₀ R C _
    (fun _ _ _ _ _ _ _ => trivial) h
  obtain ⟨s', k, -, hst, H'⟩ := Desc.foldConsOk' Hm
  obtain ⟨gs, hd⟩ := Desc.stepOk hst
  have e' : s' = t := congrArg Prod.fst (Except.ok.inj H')
  exact ⟨m, _, _, _, gs, Hp, e' ▸ hd⟩

/-- From index 1 on the hearing kinds of a link that is not the head's are of `behindKinds`. -/
theorem kindsBehind1 (sub : ModelPart) (hs : sub ≠ .head) (first : Bool) (i : ℕ) (k : KindName)
    (hi : 1 ≤ i) (hk : (kindsBeforeBatching sub first)[i]? = some k) : k ∈ Desc.K9.behindKinds := by
  have hall : ((kindsBeforeBatching sub first).drop 1).all
      (fun k => decide (k ∈ Desc.K9.behindKinds)) = true := by
    cases sub <;> cases first <;> first | decide | exact absurd rfl hs
  have hm : k ∈ (kindsBeforeBatching sub first).drop 1 := by
    refine List.mem_of_getElem? (i := i - 1) ?_
    rw [List.getElem?_drop, show 1 + (i - 1) = i by omega]
    exact hk
  exact of_decide_eq_true (List.all_eq_true.1 hall k hm)

theorem subAt_ne_head {l : ℕ} (hl : l < 24) : IM.subAt l ≠ .head := by
  unfold IM.subAt
  rw [if_neg (by omega)]
  split <;> simp

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **A hearing block behind a link's first place steps**: what the lookup on the calls was heard to
return stands, and the ledger goes on to a later one with its sizes. -/
theorem hear_steps (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (l : ℕ) (hl : l < 25) (i : ℕ) (k : KindName)
    (hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some k) (hb : k ∈ Desc.K9.behindKinds)
    (hi : 1 ≤ i) :
    ∃ b, c.blocksInOrder[14 * l + i + 2]? = some b ∧ b.Steps (Desc.K9.CF S.lookHeard?) := by
  have hlen : i < (kindsBeforeBatching (IM.subAt l) (l == 0)).length := by
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hk
    exact nomatch hk
  have h9 : (kindsBeforeBatching (IM.subAt l) (l == 0)).length ≤ 9 := by
    rw [IM.hear_len_at]
    split <;> omega
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain l _ (IM.subs_scope hS hR O l hl) i k hk
      (fun e => absurd (e ▸ hb) (by decide)) (fun e => absurd (e ▸ hb) (by decide))
      ⟨by omega, by omega⟩
  have h5 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) i] at h5
  have hp0 : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).planOk = true := O.desc ▸ hOk
  have hp : b'.planOk = true := by
    rw [← IM.alone_planOk hla]
    exact (Desc.Keeps.planOk_blocks _ hp0).1 b (List.mem_of_getElem? h5)
  have st := Desc.K9.stepsOfLot (Desc.K9.kindsStepLook Z Bs.G₀) hL hb' (l := l) (by rw [ep])
    (by rw [ep]; exact hb) hp
  exact ⟨b, h5, fun s rs gs t hy => st s rs gs t ((IM.alone_underR hla).2 s rs gs t hy)⟩

/-- **Behind the first place of a link in front of the head's the ledger is open, with its
sizes**: the frame's step "opened" has run. -/
theorem opened_sized (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 24)
    {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + 1)) s₀ R C = .ok (t, R', C')) :
    SizedAt t := by
  obtain ⟨fs, hfs, H⟩ := IM.frames_sit hS hR O
  obtain ⟨f, Lk, k, bL, b, b', bC, hf, -, -, -, -, -, hb, -, -, -, -, hy, -⟩ := H l (by omega)
  obtain ⟨s, R₁, C₁, rs, gs, -, hd⟩ := foldCut c.blocksInOrder (14 * l + 2) b hb h
  obtain ⟨m, rs', gs', -, hm⟩ := hy s rs gs t hd
  have hO : Johnson.Desc.First.Walk.OpensSized f.opened := by
    rcases IM.frames_arms hfs l f hf with ⟨X, hX, hk, -⟩ | ⟨-, P, -, -, e, -⟩ |
      ⟨P, nLin, -, -, e, -⟩ | ⟨P, -, -, e, -⟩
    · exfalso
      have e1 : (ProofFile.subsOf Z)[l]? = some (ProofFile.subOf X.kind) := by
        unfold ProofFile.subsOf
        rw [List.getElem?_map, Array.getElem?_toList, hX]
        rfl
      rw [IM.subs_scope hS hR O l (by omega), hk] at e1
      exact subAt_ne_head hl (Option.some.inj e1)
    · rw [e]
      exact Johnson.Desc.First.Walk.opensLayZero _ _ _
    · rw [e]
      exact Johnson.Desc.First.Walk.opensAtt _
    · rw [e]
      exact Johnson.Desc.First.Walk.opensLay _
  exact (hO m t hm).1

/-- **So it is behind each hearing block of such a link.** -/
theorem sized_upTo (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (l : ℕ) (hl : l < 24) : ∀ j, j < 7 → ∀ {s₀ t : S} {R R' : List Fmt.RoundView}
      {C C' : List Desc.OpenedColumn},
      Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + j + 2 + 1)) s₀ R C = .ok (t, R', C') → SizedAt t
  | 0, _, _, _, _, _, _, _, h => opened_sized hS hR O l hl h
  | j + 1, hj, s₀, t, R, R', C, C', h => by
    have hlen : j + 1 < (kindsBeforeBatching (IM.subAt l) (l == 0)).length := by
      rw [IM.hear_len_at, if_neg (by omega)]
      exact hj
    have hk := List.getElem?_eq_getElem hlen
    obtain ⟨b, hb, st⟩ := hear_steps hS hR O hOk l (by omega) (j + 1) _ hk
      (kindsBehind1 _ (subAt_ne_head hl) _ _ _ (by omega) hk) (by omega)
    obtain ⟨s, R₁, C₁, rs, gs, hf, hd⟩ := foldCut c.blocksInOrder (14 * l + (j + 1) + 2) b hb h
    obtain ⟨G, hG, hGs⟩ := sized_upTo hS hR O hOk l hl j (by omega)
      (show Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + j + 2 + 1)) s₀ R C = .ok (s, R₁, C₁) from hf)
    obtain ⟨G', h1, -, h2⟩ := (st s rs gs t hd).2 G hG hGs
    exact ⟨G', h1, h2⟩

/-- **WHAT AN ACCEPT OF A LOOKUP LEAVES, AT THE STATE THAT IS REACHED BEHIND IT**, at the 24 links
in front of the head's: something is heard at the lookup's seat, and its rows bear no entry. -/
theorem rowsBare_reached (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (l : ℕ) (hl : l < 24) (d : Bool) {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + IM.k3Ix l d + 1)) s₀ R C =
      .ok (t, R', C')) :
    ∃ g, (seatOf K3Lot.ofForm d).heard t = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of hS hR O l (by omega) d
  have h5 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix l d)] at h5
  have en : 14 * l + 2 + IM.k3Ix l d = 14 * l + IM.k3Ix l d + 2 := by omega
  rw [en] at h
  obtain ⟨s, R₁, C₁, rs, gs, hf, hd⟩ := foldCut c.blocksInOrder _ b h5 h
  have hix : IM.k3Ix l d = (if d then 6 else 1) := by
    show (if d then 6 else 1) + (if l = 24 then 1 else 0) = _
    rw [if_neg (show ¬ l = 24 by omega)]
    rfl
  have hpos : 1 ≤ IM.k3Ix l d ∧ IM.k3Ix l d ≤ 6 := by
    rw [hix]
    cases d <;> decide
  obtain ⟨G, hG, hGs⟩ := sized_upTo hS hR O hOk l hl (IM.k3Ix l d - 1) (by omega)
    (show Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + (IM.k3Ix l d - 1) + 2 + 1)) s₀ R C =
      .ok (s, R₁, C₁) by
        rw [show 14 * l + (IM.k3Ix l d - 1) + 2 + 1 = 14 * l + IM.k3Ix l d + 2 by omega]
        exact hf)
  obtain ⟨b'', h3', hk⟩ := k03_const_ok hS hR O hOk l (by omega) d
  obtain rfl : b' = b'' := Option.some.inj (h3.symm.trans h3')
  exact stated_rowsBare _ _ _ _ _ _ b' h3 hk l d rfl (K3Lot.k03_place _ _ _ _ _ l d b' h3).1 s t rs
    gs ((IM.alone_underR h4).2 s rs gs t hd) hG hGs

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.seatOf_reads
#print axioms VerifiableInference.OnPublicFiles.seatOf_fork
#print axioms VerifiableInference.OnPublicFiles.seatOf_putFork
#print axioms VerifiableInference.OnPublicFiles.seatOf_headClaim
#print axioms VerifiableInference.OnPublicFiles.stated_rowsBare
#print axioms VerifiableInference.OnPublicFiles.foldCut
#print axioms VerifiableInference.OnPublicFiles.kindsBehind1
#print axioms VerifiableInference.OnPublicFiles.subAt_ne_head
#print axioms VerifiableInference.OnPublicFiles.hear_steps
#print axioms VerifiableInference.OnPublicFiles.opened_sized
#print axioms VerifiableInference.OnPublicFiles.sized_upTo
#print axioms VerifiableInference.OnPublicFiles.rowsBare_reached
