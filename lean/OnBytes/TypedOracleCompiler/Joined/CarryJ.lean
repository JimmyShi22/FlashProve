-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/CarryJ.lean: a link with keys for the statements of a batch, over typed rounds in
which only the shared part speaks, is read over the written rounds of a file's shared chain.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


`CarryS` (OnBytes/Flat/CarrySkip.lean) has maps from written rounds to the rounds of a typed
protocol, which may lack rounds, and carries the soundness clause for one statement along them
(`backS_know`). Here the clause for the statements of a batch (`KnowJ`,
CompileK/Joined/ExtractKnow.lean; `LinkJ`, OnBytes/TypedOracleCompiler/Joined/LinkJ.lean) is carried, where on both
sides all rounds are shared and only the shared part speaks, and the maps are a function of the
statements' key. Then all slots see one written transcript and read it by one map, so a typed bad
value has the same written values over it in all slots, and the union over the slots is counted as
the typed one is.

Main names:
  `pullBad F B`: the typed bad sets B, read over the written rounds: a written verifier message is
    bad if it has an image and the image is bad; at a skipped round none is.
  `pullBad_clean`: the image of a clean written transcript is clean.
  `jWithin_pull`: the bad sets of all slots are jointly within the written errors, if the typed
    ones are within the typed errors and the written errors bear these (`CarryS.Fits`).
  `knowJ_backS`: the clause `KnowJ` of the typed reduction read on the written rounds (`backS`).
  `ofTr`, `ofTr_slot`: in such rounds each transcript is seen by all slots of some transcript of the
    whole batch. (That all slots see one transcript: the library's `slot_shared`,
    Ior/KnowBRules.lean.)
  `LinkJ.backS`: the link.

Limits: shared rounds in which only the shared part speaks, on both sides, alone: over the second
chain of a file this asks it of the joining round too (`G.aJ = RAnn.ofShared .sh G.rJ`). The maps
read a statement through its key alone, and `Fits` is asked at every key. A written verifier message
without an image (a test of work that fails) is not bad: the written transcript then has no image,
`backS` rejects, and the clause speaks of outputs alone; that is why only written messages with an
image are counted. So whoever ties a file's decision to `backS` ("where the file's verifier accepts,
no chain rejects") says with it that the file's decision rejects wherever a written verifier message
has no image. At maps under which no message has an image all is met and nothing is said. What a
skipped round sends is read by no typed verifier. Nothing here shows a clause, or maps with `Fits`,
of any protocol.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.Flat.CarrySkip
import OnBytes.TypedOracleCompiler.Joined.LinkJ
import Ior.KnowBRules

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop _root_.Prob OnBytes.Flat OnBytes.Slice
open _root_.CompileK.Joined (KnowJ)

/-- only the shared part speaks, and the verifier's messages are shared -/
abbrev shA (s : Shape) : RoundSplits s := RoundSplits.const (RAnn.ofShared .sh) s

/-! ## The bad sets -/

/-- The typed bad sets, read over the written rounds. -/
def pullBad : {s s' : Shape} → CarryS s s' → BadFam s' → BadFam s
  | _, _, .nil, _ => ()
  | _, _, .step (s := s) fm fc k, (B, κ) =>
      (fun m => {c | ∃ c', fc m c = some c' ∧ c' ∈ B (fm m)},
        fun m c => match fc m c with
          | some c' => pullBad (k m c) (κ (fm m) c')
          | none => BadFam.empty s)
  | _, _, .skip k, Bf => (fun _ => ∅, fun m c => pullBad (k m c) Bf)

/-- The image of a clean written transcript is clean. -/
theorem pullBad_clean : ∀ {s s' : Shape} (F : CarryS s s') (Bf : BadFam s') (τ : Tr s)
    (τ' : Tr s'), F.tr τ = some τ' → (pullBad F Bf).Clean τ → Bf.Clean τ'
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .step fm fc k, (B, κ), (m, c, τ), τ', h, hc => by
      have h' : ((fc m c).bind fun c' => ((k m c).tr τ).map fun t => (fm m, c', t)) = some τ' := h
      have hc1 : c ∉ {c | ∃ c', fc m c = some c' ∧ c' ∈ B (fm m)} := hc.1
      have hc2 : BadFam.Clean (match fc m c with
          | some c' => pullBad (k m c) (κ (fm m) c')
          | none => BadFam.empty _) τ := hc.2
      cases hfc : fc m c with
      | none =>
        rw [hfc] at h'
        cases h'
      | some c' =>
        rw [hfc] at h' hc2
        cases ht : (k m c).tr τ with
        | none =>
          rw [ht] at h'
          cases h'
        | some t =>
          rw [ht] at h'
          obtain rfl : (fm m, c', t) = τ' := Option.some.inj h'
          exact ⟨fun hb => hc1 ⟨c', hfc, hb⟩, pullBad_clean (k m c) _ τ t ht hc2⟩
  | _, _, .skip k, Bf, (m, c, τ), τ', h, hc => pullBad_clean (k m c) Bf τ τ' h hc.2

/-- the flag after a round: it was up, or the round's verifier message is bad -/
theorem stepOf_fst_iff {r : Round} {s : Shape} (p : Bool × BadFam (r :: s)) (m : r.Msg)
    (c : r.Chal) : (stepOf p m c).1 = true ↔ (p.1 = true ∨ c ∈ p.2.1 m) := by
  simp [stepOf]

/-- **The bad sets of all slots, read by one map, are jointly within the written errors.** -/
theorem jWithin_pull (N : ℕ) : ∀ {s s' : Shape} (F : CarryS s s') (ε : Err s') (ε' : Err s),
    F.Fits ε ε' → ∀ G : Fin N → Option (Bool × BadFam s'), JWithin N s' (shA s') ε G →
    JWithin N s (shA s) ε' fun j => (G j).map fun p => (p.1, pullBad F p.2)
  | _, _, .nil, _, _, _, _, _ => trivial
  | _, _, .step (r := r) (r' := r') (s := s) (s' := s') fm fc k, (e, ε), (e', ε'), hF, G, hG => by
      obtain ⟨⟨w, hw, hle⟩, hk⟩ := hF
      show JWithin N (r :: s) (RAnn.ofShared .sh r, shA s) (e', ε') _
      have hG' : JWithin N (r' :: s') (RAnn.ofShared .sh r', shA s') (e, ε) G := hG
      intro m0 m
      obtain ⟨h1, h2⟩ := hG' (fm m0) fun _ => ()
      have h1' : cnt (fun c' : r'.Chal => ∃ j p, G j = some p ∧ p.1 = false ∧ c' ∈ p.2.1 (fm m0))
          ≤ e := h1
      refine ⟨?_, fun v => ?_⟩
      · show cnt (fun c : r.Chal => ∃ j p,
          (G j).map (fun p => (p.1, pullBad (.step fm fc k) p.2)) = some p ∧ p.1 = false ∧
            c ∈ p.2.1 m0) ≤ e'
        refine le_trans (cnt_mono ?_) (((cnt_some_le (fc m0) (hw m0) _).trans
          (Nat.mul_le_mul_right w h1')).trans hle)
        rintro c ⟨j, p, hp, hp0, hc⟩
        obtain ⟨⟨b, B, κ⟩, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
        obtain ⟨c', hc', hb⟩ := hc
        exact ⟨c', hc', j, _, hq, hp0, hb⟩
      · cases hfc : fc m0 v with
        | none =>
          refine jWithin_of_same N s ε' (BadFam.empty s) _ (BadFam.empty_within s ε') ?_
          intro j p hp
          obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
          obtain ⟨⟨b, B, κ⟩, _, rfl⟩ := Option.map_eq_some_iff.mp hq
          show (match fc m0 v with
            | some c' => pullBad (k m0 v) (κ (fm m0) c')
            | none => BadFam.empty s) = BadFam.empty s
          rw [hfc]
        | some c' =>
          have ih := jWithin_pull N (k m0 v) ε ε' (hk m0 v) _ (h2 c')
          refine cast (congrArg (JWithin N s (shA s) ε') (funext fun j => ?_)) ih
          beta_reduce
          cases G j with
          | none => rfl
          | some q =>
            obtain ⟨b, B, κ⟩ := q
            have hiff : (c' ∈ B (fm m0)) ↔
                (v ∈ {c | ∃ c', fc m0 c = some c' ∧ c' ∈ B (fm m0)}) :=
              ⟨fun hb => ⟨c', hfc, hb⟩, fun ⟨c'', h3, hb⟩ => by
                rw [hfc] at h3
                cases h3
                exact hb⟩
            refine congrArg some (Prod.ext (Bool.eq_iff_iff.2 ?_) ?_)
            · show ((stepOf ((b, B, κ) : Bool × BadFam (r' :: s')) (fm m0) c').1 = true) ↔
                ((stepOf ((b, pullBad (.step fm fc k) (B, κ)) : Bool × BadFam (r :: s)) m0 v).1 =
                  true)
              rw [stepOf_fst_iff, stepOf_fst_iff]
              exact or_congr Iff.rfl hiff
            · show pullBad (k m0 v) (κ (fm m0) c') = (match fc m0 v with
                | some c' => pullBad (k m0 v) (κ (fm m0) c')
                | none => BadFam.empty s)
              rw [hfc]
  | _, _, .skip (r := r) (s := s) k, ε, (e', ε'), hF, G, hG => by
      show JWithin N (r :: s) (RAnn.ofShared .sh r, shA s) (e', ε') _
      intro m0 m
      refine ⟨?_, fun v => ?_⟩
      · show cnt (fun c : r.Chal => ∃ j p,
          (G j).map (fun p => (p.1, pullBad (.skip k) p.2)) = some p ∧ p.1 = false ∧
            c ∈ p.2.1 m0) ≤ e'
        refine le_trans (le_of_eq (cnt_false ?_)) (Nat.zero_le _)
        rintro c ⟨j, p, hp, _, hc⟩
        obtain ⟨q, _, rfl⟩ := Option.map_eq_some_iff.mp hp
        exact hc
      · have ih := jWithin_pull N (k m0 v) ε ε' (hF m0 v) G hG
        refine cast (congrArg (JWithin N s (shA s) ε') (funext fun j => ?_)) ih
        beta_reduce
        cases G j with
        | none => rfl
        | some q =>
          refine congrArg some (Prod.ext (Bool.eq_iff_iff.2 ?_) rfl)
          show (q.1 = true) ↔
            ((stepOf ((q.1, pullBad (.skip k) q.2) : Bool × BadFam (r :: s)) m0 v).1 = true)
          rw [stepOf_fst_iff]
          exact ⟨Or.inl, fun h => h.elim id fun hc => (hc : False).elim⟩

/-! ## The clause -/

section Know
variable {A A' B' WA' WB' κ : Type} {s : Shape} {N : ℕ}

/-- **The clause for the statements of a batch, of the typed reduction read on the written
rounds.** key: the key of a written statement; F: the maps, a function of the key; fa: the typed
statement of a written one; hadm: a vector with one key has an admissible image. -/
theorem knowJ_backS (K' : Reduction A' B') (key : A → κ) (F : κ → CarryS s K'.shape)
    (fa : A → A') {adm' : (Fin N → Option A') → Prop} {on' : A' → Prop}
    {RA' : A' → WA' → Prop} {RB' : B' → WB' → Prop} {ext' : A' → Tr K'.shape → WB' → WA'}
    {ε : Err K'.shape} {ε' : Err s} (hF : ∀ k, (F k).Fits ε ε') (tr₀ : Tr K'.shape)
    (hadm : ∀ a : Fin N → Option A, IOR.SameKey key a → adm' fun j => (a j).map fa)
    (h : KnowJ K' (shA K'.shape) N adm' on' RA' RB' ext' ε) :
    KnowJ (backS K' (fun a => F (key a)) fa) (shA s) N (IOR.SameKey key) (fun a => on' (fa a))
      (fun a w => RA' (fa a) w) RB'
      (fun a τ w => ext' (fa a) (((F (key a)).tr τ).getD tr₀) w) ε' := by
  obtain ⟨bad', c', J'⟩ := h
  refine ⟨fun a => pullBad (F (key a)) (bad' (fa a)), ?_, ?_⟩
  · intro a τ b w ha hτ hb hw
    have hb' : ((F (key a)).tr τ).bind (K'.out (fa a)) = some b := hb
    cases ht : (F (key a)).tr τ with
    | none =>
      rw [ht] at hb'
      cases hb'
    | some τ' =>
      rw [ht] at hb'
      show RA' (fa a) (ext' (fa a) (((F (key a)).tr τ).getD tr₀) w)
      rw [ht]
      exact c' (fa a) τ' b w ha (pullBad_clean _ _ τ τ' ht hτ) hb' hw
  · intro a ha
    by_cases hne : ∃ j aj, a j = some aj
    · obtain ⟨j₀, a₀, h₀⟩ := hne
      have ih := jWithin_pull N (F (key a₀)) ε ε' (hF _) _ (J' _ (hadm a ha))
      refine cast (congrArg (JWithin N s (shA s) ε') (funext fun j => ?_)) ih
      beta_reduce
      cases hj : a j with
      | none => rfl
      | some aj =>
        show some (false, pullBad (F (key a₀)) (bad' (fa aj))) =
          some (false, pullBad (F (key aj)) (bad' (fa aj)))
        rw [ha j j₀ aj a₀ hj h₀]
    · refine jWithin_of_same N s ε' (BadFam.empty s) _ (BadFam.empty_within s ε') fun j p hp => ?_
      obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact absurd ⟨j, aj, haj⟩ hne

end Know

/-! ## One transcript for all slots -/

/-- A transcript, as one of the whole batch. -/
def ofTr (N : ℕ) : (s : Shape) → Tr s → BTr N s (shA s)
  | [], _ => ()
  | _ :: s, (m, c, τ) => ((m, fun _ => ()), c, ofTr N s τ)

theorem ofTr_slot {N : ℕ} (j : Fin N) : ∀ (s : Shape) (τ : Tr s), (ofTr N s τ).slot j = τ
  | [], _ => rfl
  | r :: s, (m, c, τ) => by
    show ((RAnn.ofShared .sh r).join m (), c, BTr.slot j (ofTr N s τ)) = (m, c, τ)
    rw [ofTr_slot j s τ]
    rfl

/-! ## The link -/

/-- **A link with keys over typed rounds in which only the shared part speaks, read over the written
rounds of a shared chain.** g: the typed key of a written statement's image is a function of the
written key. -/
theorem LinkJ.backS {A A' B' WA' WB' κ κ' κ₂ : Type} {s : Shape} {N : ℕ} {K' : Reduction A' B'}
    {key' : A' → κ'} {key₂ : B' → κ₂} {on' : A' → Prop} {RA' : A' → WA' → Prop}
    {RB' : B' → WB' → Prop} {ext' : A' → Tr K'.shape → WB' → WA'} {ε : Err K'.shape}
    (h : LinkJ K' (shA K'.shape) N key' key₂ on' RA' RB' ext' ε) (key : A → κ)
    (F : κ → CarryS s K'.shape) (fa : A → A') {ε' : Err s} (hF : ∀ k, (F k).Fits ε ε')
    (tr₀ : Tr K'.shape) (g : κ → κ') (hg : ∀ a, key' (fa a) = g (key a)) :
    LinkJ (OnBytes.Flat.backS K' (fun a => F (key a)) fa) (shA s) N key key₂
      (fun a => on' (fa a)) (fun a w => RA' (fa a) w) RB'
      (fun a τ w => ext' (fa a) (((F (key a)).tr τ).getD tr₀) w) ε' := by
  have hadm : ∀ a : Fin N → Option A, IOR.SameKey key a →
      IOR.SameKey key' fun j => (a j).map fa := by
    intro a ha j j' x x' hx hx'
    obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨aj', haj', rfl⟩ := Option.map_eq_some_iff.mp hx'
    rw [hg, hg, ha j j' aj aj' haj haj']
  refine ⟨knowJ_backS K' key F fa hF tr₀ hadm h.know, fun a ha τ j j' b b' hb hb' => ?_⟩
  obtain ⟨aj, haj, ho⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨aj', haj', ho'⟩ := Option.bind_eq_some_iff.1 hb'
  have ho1 : ((F (key aj)).tr (τ.slot j)).bind (K'.out (fa aj)) = some b := ho
  have ho2 : ((F (key aj')).tr (τ.slot j')).bind (K'.out (fa aj')) = some b' := ho'
  have hs : BTr.slot j' τ = BTr.slot j τ := _root_.Iop.slot_shared N s τ j' j
  rw [← ha j j' aj aj' haj haj', hs] at ho2
  obtain ⟨τ', ht, hk⟩ := Option.bind_eq_some_iff.1 ho1
  rw [ht] at ho2
  have hk' : K'.out (fa aj') τ' = some b' := ho2
  refine h.adm _ (hadm a ha) (ofTr N K'.shape τ') j j' b b' ?_ ?_
  · show ((a j).map fa).bind (fun x => K'.out x ((ofTr N K'.shape τ').slot j)) = some b
    rw [haj, ofTr_slot]
    exact hk
  · show ((a j').map fa).bind (fun x => K'.out x ((ofTr N K'.shape τ').slot j')) = some b'
    rw [haj', ofTr_slot]
    exact hk'

end TypedOracleCompiler.Joined
