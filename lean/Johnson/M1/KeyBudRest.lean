-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: the second part's bound where no tree of the job has a number that the part sends.
/-
Johnson/M1/KeyBudRest.lean: own_reads_apart, bud_own_apart, bud_rest_apart of Johnson/M1/BudTestO.lean, word for word, in this namespace: general in
the file. They are copied because that file stands on the proof file's own facts.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.DebtAtO
import Johnson.Desc.ProofFile.Honest.K12.Sim.AloneAtU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.KeyRest
open ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open OnBytes.LinkSim.AtText (oNext)
open ProofFile.Honest.K12.Light

variable {W X Pb : Type}

/-- `own_reads_tr`, where no tree of the job has the number of the tree that round r sends. -/
theorem own_reads_apart (J : TestJob W X) (decls : List Fmt.DeclaredRound) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource) (sent chain firstTree : ℕ) (F : OpensFit J decls depths src₀ sent)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest)
    (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) (D : ℕ → Fmt.Drawn)
    (Rs : List Fmt.Drawn) (hD : ∀ n (h : n < Rs.length), Rs[n] = D n) (r : ℕ)
    (hr : (depthAt J r).isSome = true)
    (apart : ∀ k, k < depths.length → ∀ n, srcOf chain (src₀ k) = (chain, n) → n ≠ sent + sentBefore J r) :
    ∀ q ∈ readsOf chain firstTree stored tree decls Rs,
      q.src = some (chain, sent + sentBefore J r) → q.pos ∈ openedTr D rest s 1 (r - 1) := by
  intro q hq hsrc
  obtain ⟨x', hx', h1, h2⟩ := reads_plan chain firstTree stored tree D decls Rs 0 F.stored
    (fun n hn => by rw [Nat.zero_add]; exact hD n hn) q hq
  rw [F.opens] at hx'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
  rw [hsrc] at h1
  have h1' : (chain, sent + sentBefore J r) = srcOf chain (srcBy J src₀ sent x.2.2) :=
    Option.some.inj h1
  have hx0 := hx
  unfold opensTest at hx
  rw [hst] at hx
  rcases opens_tr D rest s 1 (frontTrees depths) x hx with ⟨y, hy, rfl⟩ | ⟨r', hr', hle, he⟩
  · exfalso
    unfold frontTrees at hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have hk := (F.olds _ hx0 z.2 rfl).1
    exact apart z.2 hk _ h1'.symm rfl
  · rw [hr'] at h1'
    have e : sent + sentBefore J r = sent + sentBefore J r' := congrArg Prod.snd h1'
    have hs' := (F.senders x hx0 r' hr').2
    obtain rfl := sentBefore_inj J r r' hr hs' (by omega)
    rw [← he]
    exact h2

/-- `bud_own`, at the same premise at the rounds that the second part sends at. -/
theorem bud_own_apart (J : TestJob W X) (decls : List Fmt.DeclaredRound) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource) (sent chain firstTree : ℕ) (F : OpensFit J decls depths src₀ sent)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g)
    (apart : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      ∀ k, k < depths.length → ∀ n, srcOf chain (src₀ k) = (chain, n) →
        n ≠ sent + sentBefore J (firstLen J.p.nums.stages + i))
    (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table))
    (ds₁ ds : List Fmt.Drawn) (h1 : ds₁.length = firstLen J.p.nums.stages) (roots : List ℕ)
    (hroots : ∀ i, i < roots.length → roots.getD i 0 =
      if (depthAt J (firstLen J.p.nums.stages + i)).isSome = true then 1 else 0) :
    budOpened J.p.nums.stages 1 ds
      (asksFrom (fun m => ((readsOf chain firstTree stored tree decls (ds₁ ++ ds)).filter fun q =>
        q.src == some (chain, m)).map (·.pos)) roots
        (sent + sentBefore J (firstLen J.p.nums.stages))) := by
  refine bud_of_asksFrom _ ds _ roots _ fun i hi q hq => ?_
  have hil : i < roots.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hi
    omega
  have hsome : (depthAt J (firstLen J.p.nums.stages + i)).isSome = true := by
    have h := hroots i hil
    by_contra hc
    rw [if_neg hc] at h
    omega
  rw [Nat.add_assoc, sent_sum J _ roots hroots i (Nat.le_of_lt hil)] at hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
  obtain ⟨hm, hs⟩ := List.mem_filter.1 hq'
  have h := own_reads_apart J decls depths src₀ sent chain firstTree F s (next :: rest) hst stored
    tree (fun n => (ds₁ ++ ds).getD n noDraw) (ds₁ ++ ds)
    (fun n hn => (List.getD_eq_getElem _ _ hn).symm) (firstLen J.p.nums.stages + i) hsome
    (apart i hsome) q' hm (eq_of_beq hs)
  have hn₀ : firstLen J.p.nums.stages = 2 + s.k := by rw [hst]; rfl
  have e : firstLen J.p.nums.stages + i - 1 = 1 + ((H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) + i := by
    rw [hn₀, hk]
    omega
  rw [e] at h
  have hc : openedTr (laterOf J.p.nums.stages ds) (next :: rest) s 1
      (1 + ((H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) + i) =
      openedTr (fun n => (ds₁ ++ ds).getD n noDraw) (next :: rest) s 1
        (1 + ((H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) + i) :=
    openedTr_congr _ _ (next :: rest) s 1 _ fun n hn => by
      unfold oNext at hn
      show ds.getD (n - firstLen J.p.nums.stages) noDraw = (ds₁ ++ ds).getD n noDraw
      rw [List.getD_append_right _ _ _ _ (by rw [h1, hn₀, hk]; omega), h1]
  have hd : J.p.nums.stages.drop 1 = next :: rest := by rw [hst]; rfl
  have hh : J.p.nums.stages.headD default = s := by rw [hst]; rfl
  rw [hd, hh, hc]
  exact h

/-- `bud_rest_file`, at the same premise. -/
theorem bud_rest_apart {Xi V : Type} {F : VerifiableInference.Desc.FileDescription Xi} (J : TestJob W X) (Js : SimJob Pb)
    (pre t : List (VerifiableInference.Desc.Block F.S₂ F.Cl)) (b : VerifiableInference.Desc.Block F.S₂ F.Cl)
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (sent : ℕ)
    (O : OpensFit J b.rounds depths src₀ sent) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest)
    (hk : s.k = (H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) (hT : tablesFitB J = true)
    (apart : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      ∀ k, k < depths.length → ∀ n, srcOf 1 (src₀ k) = (1, n) →
        n ≠ sent + sentBefore J (firstLen J.p.nums.stages + i))
    (hlen : b.rounds.length = J.laid.length)
    (hen : firstLen J.p.nums.stages ≤ J.laid.length) (ρ : Draws) (hρ : ρ.due F = true)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneB F pre t (sent + sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    budOpened J.p.nums.stages 1
      ((ρ.shared.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
        (restMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks F ρ 1) ((restMember (V := V) J Js).rounds.map (·.2.length))
        (sent + sentBefore J (firstLen J.p.nums.stages))) := by
  have hρ' := hρ
  unfold Draws.due at hρ'
  simp only [Bool.and_eq_true] at hρ'
  have h2 : drawsFit (F.shared.blocksInOrder.flatMap (·.rounds)) ρ.shared = true := hρ'.1.1.2
  have htot := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at htot
  have hrl : (restMember (V := V) J Js).rounds.length =
      b.rounds.length - firstLen J.p.nums.stages := by
    show (J.laid.drop (firstLen J.p.nums.stages)).length = _
    rw [List.length_drop, hlen]
  have hds : (ρ.shared.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
      (restMember (V := V) J Js).rounds.length =
      (((ρ.shared.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).drop
        (firstLen J.p.nums.stages)) := by
    rw [List.drop_take, List.drop_drop, hrl]
  have h1 : (((ρ.shared.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take, List.length_take, List.length_drop]
    omega
  rw [hds]
  refine bud_sub _ _ _ _ _ _ (bud_own_apart J b.rounds depths src₀ sent 1 0 O s next
    rest hst hk apart (fun _ _ => none) (fun _ => none) _ _ h1 _
    fun i hi => roots_fit J hT _ i hi) fun i hi q hq => ?_
  rw [List.take_append_drop]
  have hil : i < ((restMember (V := V) (Pb := Pb) J Js).rounds.map (·.2.length)).length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hi
    omega
  have hroots : ∀ i, i < ((restMember (V := V) J Js).rounds.map (·.2.length)).length →
      ((restMember (V := V) J Js).rounds.map (·.2.length)).getD i 0 =
        if (depthAt J (firstLen J.p.nums.stages + i)).isSome = true then 1 else 0 :=
    fun i hi => roots_fit J hT _ i hi
  have hsome : (depthAt J (firstLen J.p.nums.stages + i)).isSome = true := by
    have h := hroots i hil
    by_contra hc
    rw [if_neg hc] at h
    omega
  rw [Nat.add_assoc, sent_sum J _ _ hroots i (Nat.le_of_lt hil)] at hq ⊢
  exact asks_in_block pre t b hcut ρ hρ _ (ha i hsome) q hq

end ProofFile.Honest.K12.KeyRest

#print axioms ProofFile.Honest.K12.KeyRest.bud_rest_apart
