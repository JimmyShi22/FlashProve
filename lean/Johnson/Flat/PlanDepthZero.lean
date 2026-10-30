-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/PlanDepthZero.lean: in the chains that the verifier program's planner makes of three
public files, the key's binding tree has one leaf, if the parameter bytes of the key's one-time
chain are fewer than 2 ^ 64. So at the data made of three public files (`bigZFull Z`,
`bigZSmall Z`) the depth of the request tree of the key file's calls in the written wiring is 0.

Theorems and one test; names no hash function. Johnson/Flat/WireDepthZero.lean has that depth 0
where the program's check of a key file said yes. Here no file but the three public ones is read
and no check is run. How: the planner writes the shape of a key's binding tree with depth 0
(`Plan.KeySized.binding`, OnBytes/Plan/KeyOneTime.lean), spells it into the parameter bytes of the
key's one-time chain, and reads these bytes back; the chains in its answer are what was read back.

Main names:
  `Params.readBinding_zero`: what is read from an item "binding tree" that was spelled from a tree
    of depth 0 has depth 0.
  `Model.Verify.planned_key_oneLeaf`: where `planned` returned p and the one-time chain's parameter
    bytes are fewer than 2 ^ 64: `p.chains.key.oneTime.binding.logLeaves = 0`.
  `keyBytesFitB Z`: the condition on the bytes as a test on three public files; yes where the
    planner refuses.
  `bigZFull_oneLeaf`, `bigZSmall_oneLeaf`: where that test says yes: the depth is 0 in
    `(bigZFull Z).k` | `(bigZSmall Z).k`; also where the planner refuses (the fixed record).
  `wireFullAt_depthT_own`, `wireSmallAt_depthT_own`: there the wiring's field `depthReqT` is 0.

Limits: THE CONDITION ON THE BYTES IS A PREMISE. "Wherever the planner returns", with nothing
beside it, is not shown: the law by which spelled items are read back as they were spelled
(`Params.Given.read_items`, OnBytes/Params/ReadBackLaws.lean) asks it, since a length from 2 ^ 64 on
is spelled modulo 2 ^ 64; no theorem bounds the planner's bytes, and neither the planner nor the
tests `ownFullAtB` | `ownSmallAtB` (Johnson/Top/ArmsAtFiles.lean, ArmsAtFilesSmall.lean) ask it.
That `keyBytesFitB` says yes at any files is a value that an evaluation can give; nothing is
evaluated here. A, E, P are letters. No file calls these theorems yet. The hypothesis
`CompilerSoundnessConditionStatements.keySound` is neither named nor rewritten. "The program" is `verify-on-bytes`, the verifier
written in Lean. Nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.WireDepthZero
import Johnson.Top.ArmsAtFiles
import Johnson.Top.ArmsAtFilesSmall
import OnBytes.TieK.ChainsRead

set_option autoImplicit false

namespace OnBytes.Params

/-- What is read from an item "binding tree" that was spelled from a tree of depth 0 has depth 0. -/
theorem readBinding_zero {s : ℕ} {B : LinBindingShape}
    (h : readBinding (spellBinding ⟨0, s⟩) = some B) : B.logLeaves = 0 := by
  have e : spellBinding ⟨0, s⟩ = Fmt.u64 (UInt64.ofNat 0) ++ Fmt.cat [spellWord s] := by
    show Fmt.cat (spellWord 0 :: [spellWord s]) = _
    rw [Fmt.cat_cons]
    rfl
  have w : Fmt.wordAt (Fmt.u64 (UInt64.ofNat 0) ++ Fmt.cat [spellWord s]) 0 = UInt64.ofNat 0 := by
    have := Fmt.wordAt_mid ByteArray.empty (Fmt.u64 (UInt64.ofNat 0)) (Fmt.cat [spellWord s]) 0
      (by rw [Fmt.size_u64])
    rw [← Fmt.wordAt_u64 (UInt64.ofNat 0)]
    simpa using this
  rw [e] at h
  unfold readBinding Cut.whole Fmt.whole Cut.rd at h
  split at h
  · rename_i x j hx
    split at h
    · cases h
      unfold bindingShape at hx
      obtain ⟨d, j1, h1, hx⟩ := cut_bind hx
      obtain ⟨y, j2, _, hx⟩ := cut_bind hx
      cases hx
      obtain ⟨rfl, -⟩ := word_at h1
      show (Fmt.wordAt (Fmt.u64 (UInt64.ofNat 0) ++ Fmt.cat [spellWord s]) 0).toNat = 0
      rw [w]
      rfl
    · cases h
  · cases h

end OnBytes.Params

namespace OnBytes.Model.Verify

open OnBytes.Params (exc_bind)

/-- **In the planner's answer the key's binding tree has one leaf**, if the parameter bytes of the
key's one-time chain are fewer than 2 ^ 64. -/
theorem planned_key_oneLeaf {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) (hb : (p.chains.bytes .keyOneTime).size < 2 ^ 64) :
    p.chains.key.oneTime.binding.logLeaves = 0 := by
  have h32 := (planned_spelled h).1
  obtain ⟨r1, -, -⟩ := planned_read h
  have hm : ∃ l x bits, Params.configure l x p.cfg bits = .ok p.chains.made := by
    unfold planned at h
    obtain ⟨X, _, h⟩ := exc_bind h
    dsimp only at h
    obtain ⟨chains, hc, h⟩ := exc_bind h
    obtain ⟨_, _, h⟩ := exc_bind h
    cases h
    obtain ⟨shapes, hm⟩ := chainsOf_made hc
    exact ⟨_, _, _, hm⟩
  obtain ⟨l, x, bits, hm⟩ := hm
  obtain ⟨-, ⟨P1, e1⟩, -, -⟩ := Params.configure_items hm
  obtain ⟨m, r, t, c, ll, F⟩ := TieK.oneTime_read_open (Params.KeyChains.read_parts r1).1
  have g1 := F.given
  have b1 : p.chains.bytes .keyOneTime = p.chains.made.keyOneTime := rfl
  rw [b1, e1] at g1 hb
  have t1 := Params.Given.read_items hb h32 (by
    intro y hy
    simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)) g1
  have q1 := F.items
  rw [t1] at q1
  simp only [Plan.oneTimeItems, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at q1
  have w := F.binding
  rw [← q1.2.2.1] at w
  exact Params.readBinding_zero w

end OnBytes.Model.Verify

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Flat OnBytes.Slice OnBytes.K OnBytes.K.ArmsAtFiles

/-- The condition on the bytes, as a test on three public files: the parameter bytes of the key's
one-time chain in the planner's answer are fewer than 2 ^ 64. Yes where the planner refuses. -/
def keyBytesFitB (Z : Pub) : Bool :=
  match planOf Z with
  | .ok p => decide ((p.chains.bytes .keyOneTime).size < 2 ^ 64)
  | .error _ => true

/-- Where the planner returns p at Z and the test says yes, the key's binding tree has one leaf. -/
theorem planOf_key_oneLeaf {Z : Pub} {p : Model.Verify.Planned} (hp : planOf Z = .ok p)
    (t : keyBytesFitB Z = true) : p.chains.key.oneTime.binding.logLeaves = 0 := by
  unfold keyBytesFitB at t
  rw [hp] at t
  exact Model.Verify.planned_key_oneLeaf hp (of_decide_eq_true t)

/-- **At the data made of three public files the key's binding tree has one leaf**, at the full
size, where the test on the bytes says yes. Where the planner refuses, of the fixed record. -/
theorem bigZFull_oneLeaf {Z : Pub} (t : keyBytesFitB Z = true) :
    (bigZFull Z).k.oneTime.binding.logLeaves = 0 := by
  cases hp : planOf Z with
  | ok p =>
    rw [bigZFull_of hp]
    exact planOf_key_oneLeaf hp t
  | error e =>
    unfold bigZFull
    rw [hp]
    rfl

/-- The same at the small size. -/
theorem bigZSmall_oneLeaf {Z : Pub} (t : keyBytesFitB Z = true) :
    (bigZSmall Z).k.oneTime.binding.logLeaves = 0 := by
  cases hp : planOf Z with
  | ok p =>
    rw [bigZSmall_of hp]
    exact planOf_key_oneLeaf hp t
  | error e =>
    unfold bigZSmall
    rw [hp]
    rfl

/-- **There the key file's request tree in the written wiring has one leaf**, at the full size. -/
theorem wireFullAt_depthT_own {Z : Pub} (t : keyBytesFitB Z = true)
    (A : (frS.toDecR frZ 402653181).Claims Flat.Req) (E : Coding A)
    (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigZFull Z)).Provers) (salt : ℕ) :
    (wireFullAt A E (bigZFull Z) P salt).depthReqT = 0 :=
  (wireFullAt_depths A E (bigZFull Z) P salt).2.1.trans (bigZFull_oneLeaf t)

/-- The same at the small size. -/
theorem wireSmallAt_depthT_own {Z : Pub} (t : keyBytesFitB Z = true)
    (A : (srS.toDecR srZ 524285).Claims (ReqAt sizesSmall)) (E : Coding A)
    (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigZSmall Z)).Provers) (salt : ℕ) :
    (wireSmallAt A E (bigZSmall Z) P salt).depthReqT = 0 :=
  (wireSmallAt_depths A E (bigZSmall Z) P salt).2.1.trans (bigZSmall_oneLeaf t)

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Params.readBinding_zero
#print axioms OnBytes.Model.Verify.planned_key_oneLeaf
#print axioms VerifiableInference.OnPublicFiles.planOf_key_oneLeaf
#print axioms VerifiableInference.OnPublicFiles.bigZFull_oneLeaf
#print axioms VerifiableInference.OnPublicFiles.bigZSmall_oneLeaf
#print axioms VerifiableInference.OnPublicFiles.wireFullAt_depthT_own
#print axioms VerifiableInference.OnPublicFiles.wireSmallAt_depthT_own
