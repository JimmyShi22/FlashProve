-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinAsked.lean: the evaluable form of the compiled verifier gives one verdict at two families of
oracle functions that agree on the queries it asks (`verifyP_asked`, under the hypotheses of its
statement).

The compiled verifier (`Compile.Batch.verifyOneProtocol`) has a form that can be evaluated, `verifyP`
(Run/ThinDefs.lean; "thin" in names). It is given a family of typed oracle functions. This file
compares its runs at two families g and g' that agree at every query which passes a test, except for
the message blocks of round 0.

Why this is needed. A family answers a chain query by a pair: the blocks of the verifier's message,
and the chain value. Two families can give one chain value at round 0 and different blocks there
(one of them answers blocks that have no call by zeros). So they do not "agree at that query", and a
congruence along the asked queries (Run/DetAlong.lean) does not reach them. The chain reads an
answer only through the wiring's function of the blocks (the map from hash output to a challenge)
and through the chain value. Where the first round's wiring does not look at its blocks, the
difference is not seen.

1. What the file contains (definitions that compute).
   `askP`.
   `FrontBlind`: The wiring of the first round gives one verifier's message at all blocks. (It is
     stated so, not through the message's type.) It is a proposition, not a test that computes.
   `askedP`. (Node queries are two digests: there is no test for them.)

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   `chainP_ask`.
   `runForestP_ask`, `runForestsP_ask`: The walks through the trees: one node function, and one
     answer at the leaf queries of the forests' checks, imply `runForestP` (`runForestsP`) at g = at
     g'.
   `verifyP_asked`: `askedP` at g (`ha`), the agreements where the tests hold (`hP`, `hL`), one node
     function (`hn`) and `FrontBlind` (`hw`) imply `verifyP` at g = `verifyP` at g'.

4. What is not claimed.
   That the test `askedP` holds for any string.
   As it is written, `askedP` is no test for an evaluator at rounds that draw field elements (tried
   once at a description with such rounds: it ran into the memory limit). It is built on `chainP`,
   `strictP` and `forestsOfP`, the forms that are meant for proofs (see part 4 of the head of
   Run/ThinDefs.lean).
   No statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
import Run.ThinDefs

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

section
variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X) (g g' : Fam (spec lam K (Lf ())))

/-- Every chain query that the chain forms at g passes the test; a joining round: false. -/
def askP (early : X → X) (late : Option ℕ) (t : Tag) (Pq : FbIn lam (Lf ()) t → Bool)
    (cms : List (Dig lam)) (x : Option X) (salt : Bits) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    (PlainPart (up S) A → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) →
    ℕ → Phase lam → List (Dig lam) → Plains (up S) → Bool
  | [], _, _, _, _, _, _, _ => true
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.hasJ rts with
          | some (rt, rts') =>
              Pq ⟨i, h.withLate (if late = some i then x else none),
                rt, embP (.inl (.inr (a.plain pl).2))⟩ &&
              askP early late t Pq cms x salt S A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn
                  (g (OracleName.fb t)
                    (⟨i, h.withLate (if late = some i then x else none),
                      rt,
                      embP (.inl (.inr
                            (a.plain
                              pl).2))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2))
                rts' pls
          | none => true
      | some (.one h false next) =>
          match takeRt w.has0 rts with
          | some (rt, rts') =>
              Pq ⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ &&
              askP early late t Pq cms x salt S A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn
                  (g (OracleName.fb t)
                    (⟨i, h, rt,
                      embP (.inl (.inl
                            (a.plain
                              pl).1))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2))
                rts' pls
          | none => true
      | some (.join _) => false
      | none => true

/-- The wire of the first of some rounds does not look at its blocks. -/
def FrontBlind : (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → Prop
  | [], _, _ => True
  | _ :: _, (_, _), (w, _) => ∀ u u' : Fin K → Dig lam, w.chal u = w.chal u'

/-- The chain at two families. If, where a query passes the test, the two give one chain value, and
one whole answer if the round is not 0 (`hP`); if every query formed passes and no joining round is
met (`askP .. = true`); and if, at i = 0, the front wire (round 0) does not look at its blocks: then
`chainP` at g is `chainP` at g'. -/
theorem chainP_ask (early : X → X) (late : Option ℕ) (t : Tag) (Pq : FbIn lam (Lf ()) t → Bool)
    (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam)
    (hP : ∀ q : FbIn lam (Lf ()) t, Pq q = true →
      (g (OracleName.fb t) q : (Fin K → Dig lam) × Dig lam).2 =
        (g' (OracleName.fb t) q : (Fin K → Dig lam) × Dig lam).2 ∧
      (q.round ≠ 0 → g (OracleName.fb t) q = g' (OracleName.fb t) q)) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (embP : PlainPart (up S) A → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) (i : ℕ) (ph : Phase lam)
        (rts : List (Dig lam)) (pls : Plains (up S)),
      (i = 0 → FrontBlind S A W) →
      askP Lf g early late t Pq cms x salt S A W embP i ph rts pls = true →
      chainP Lf g early late t cms x salt rtreq S A W embP i ph rts pls =
        chainP Lf g' early late t cms x salt rtreq S A W embP i ph rts pls
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls), hw, ha => by
    have hc : ∀ q : FbIn lam (Lf ()) t, q.round = i → Pq q = true →
        w.chal (g (OracleName.fb t) q : (Fin K → Dig lam) × Dig lam).1 =
          w.chal (g' (OracleName.fb t) q : (Fin K → Dig lam) × Dig lam).1 := by
      intro q hq hp
      by_cases h0 : i = 0
      · exact hw h0 _ _
      · rw [(hP q hp).2 (hq ▸ h0)]
    simp only [chainP]
    simp only [askP] at ha
    split
    · rename_i h next e
      rw [e] at ha
      simp only at ha
      split
      · rename_i rt rts' e2
        rw [e2] at ha
        simp only [Bool.and_eq_true] at ha
        rw [hc _ rfl ha.1, ← (hP _ ha.1).1,
          chainP_ask early late t Pq cms x salt rtreq hP S A W _ (i + 1) _ _ pls
            (fun h => absurd h (Nat.succ_ne_zero i)) ha.2]
      · rfl
    · rename_i h next e
      rw [e] at ha
      simp only at ha
      split
      · rename_i rt rts' e2
        rw [e2] at ha
        simp only [Bool.and_eq_true] at ha
        rw [hc _ rfl ha.1, ← (hP _ ha.1).1,
          chainP_ask early late t Pq cms x salt rtreq hP S A W _ (i + 1) _ _ pls
            (fun h => absurd h (Nat.succ_ne_zero i)) ha.2]
      · rfl
    · rename_i ρ e
      rw [e] at ha
      cases ha
    · rfl

/-! ### The walks up the Merkle trees -/

theorem runForestP_ask (hn : ∀ a b, nodeP Lf g a b = nodeP Lf g' a b) (F : Forest lam (Lf ()))
    (hl : ∀ e ∈ F.cs, (g OracleName.leaf e.2.inp : Dig lam) = g' OracleName.leaf e.2.inp) (s : List (Dig lam)) :
    runForestP Lf g F s = runForestP Lf g' F s := by
  have e1 : nodeP Lf g = nodeP Lf g' := by
    funext a b
    exact hn a b
  have e2 : (F.cs.map fun e => (g OracleName.leaf e.2.inp : Dig lam)) =
      F.cs.map fun e => (g' OracleName.leaf e.2.inp : Dig lam) :=
    List.map_congr_left hl
  unfold runForestP
  rw [e1]
  exact congrArg
    (fun v =>
      ((Octopus.upN F.depth (idxP Lf F)).zip
          (Octopus.octF (nodeP Lf g') F.depth (idxP Lf F) v s)).all
        fun m => decide (m.2 = F.treeRoot m.1)) e2

theorem runForestsP_ask (hn : ∀ a b, nodeP Lf g a b = nodeP Lf g' a b) :
    ∀ (Fs : List (Forest lam (Lf ()))),
      (∀ c ∈ flatP Lf Fs, (g OracleName.leaf c.inp : Dig lam) = g' OracleName.leaf c.inp) →
      ∀ s : List (Dig lam), runForestsP Lf g Fs s = runForestsP Lf g' Fs s
  | [], _, _ => rfl
  | F :: Fs, hl, s => by
    simp only [runForestsP]
    rw [runForestP_ask Lf g g' hn F (fun e he => hl e.2 (by
        unfold flatP
        rw [List.flatMap_cons]
        exact List.mem_append_left _ (List.mem_map_of_mem he))),
      runForestsP_ask hn Fs (fun c hc => hl c (by
        unfold flatP at hc ⊢
        rw [List.flatMap_cons]
        exact List.mem_append_right _ hc))]

/-! ### The verifier -/

variable {Y : Type} {E : ExtSpec}

/-- The test on an argument string: `verifyP` at g asks nothing but what passes: every chain query
passes `Pq`; the chain does not join; and, if the strict format holds, every leaf query passes `Pl`.
(Node queries are two digests: no test.) -/
def askedP (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag)
    (Pq : FbIn lam (Lf ()) t → Bool) (Pl : LeafIn (Lf ()) → Bool) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Bool :=
  askP Lf g early late t Pq cms (xin x) π.salt P.S P.ann wq.sh embP 0 .first π.roots π.plains &&
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => true
  | some (ρ, rts, ph) =>
      !strictP sMT sFS P wq depthReq x π ρ rts ph ||
      (ph.slotVal.isNone && match forestsOfP Lf P wq embS embE cms x π ρ rts with
        | none => true
        | some Fs => (flatP Lf Fs).all fun c => Pl c.inp)

/-- `verifyP` at two families that agree where the tests hold, but for the message blocks of round
0: under `hP`, `hL`, `hn`, `hw` and `ha` the two verdicts are equal. -/
theorem verifyP_asked (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag)
    (Pq : FbIn lam (Lf ()) t → Bool) (Pl : LeafIn (Lf ()) → Bool)
    (hP : ∀ q : FbIn lam (Lf ()) t, Pq q = true →
      (g (OracleName.fb t) q : (Fin K → Dig lam) × Dig lam).2 =
        (g' (OracleName.fb t) q : (Fin K → Dig lam) × Dig lam).2 ∧
      (q.round ≠ 0 → g (OracleName.fb t) q = g' (OracleName.fb t) q))
    (hL : ∀ q : LeafIn (Lf ()), Pl q = true → (g OracleName.leaf q : Dig lam) = g' OracleName.leaf q)
    (hn : ∀ a b, nodeP Lf g a b = nodeP Lf g' a b) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (hw : FrontBlind P.S P.ann wq.sh) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) (xin : Y → Option X)
    (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up)
    (ha : askedP Lf g early late sMT sFS t Pq Pl P wq embS embP xin embE depthReq cms x π = true) :
    verifyP Lf g early late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      verifyP Lf g' early late sMT sFS t P wq embS embP xin embE depthReq cms x π := by
  unfold askedP at ha
  rw [Bool.and_eq_true] at ha
  have hc := chainP_ask Lf g g' early late t Pq cms (xin x) π.salt π.rtreq hP P.S P.ann wq.sh embP 0
    .first π.roots π.plains (fun _ => hw) ha.1
  have h2 := ha.2
  unfold verifyP
  rw [← hc]
  cases hch : chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    rw [hch] at h2
    simp only at h2 ⊢
    by_cases hs : strictP sMT sFS P wq depthReq x π ρ rts ph = true
    · rw [if_pos hs, if_pos hs]
      rw [hs] at h2
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h2
      have hph : ph.slotVal = none := by simpa using h2.1
      unfold afterP
      cases hf : forestsOfP Lf P wq embS embE cms x π ρ rts with
      | none => rfl
      | some Fs =>
        have h3 := h2.2
        rw [hf] at h3
        simp only [List.all_eq_true] at h3
        simp only
        rw [runForestsP_ask Lf g g' hn Fs (fun c hc => hL _ (h3 c hc))]
        unfold reqPartP
        rw [hph]
    · rw [if_neg hs, if_neg hs]

end

end Run.Thin
