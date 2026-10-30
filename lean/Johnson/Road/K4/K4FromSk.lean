-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4FromSk.lean: what K4's lot lays, as a function of five plain things.

What it is for. `ProofFile.k4From Z G …` (Johnson/Desc/ProofFile/Lot/K4.lean) lays the pairs from which
K4's sub-protocols are made. It takes the whole public part Z and the whole ground G. Here stands a
twin, `k4FromSk`, that takes what the pairs' plain fields hang on and nothing else: the table of
steps · the first chain's declared rounds' entries · how many groups have a plan · of each segment,
whether it is a layers' segment, and then its group and name. And the law that the twin gives the
pairs' plain fields (`k4ViewOf`: the Bool · name · link · piece · `before` · group). So Lean's
kernel can evaluate the twin at written values.

What it says.
  `k4Sent_eq`     ProofFile.k4Sent Z link = sentListOn Z.cuts (Z.D.1.map (·.entry)) link, at all letters.
  `k4From_view`   (k4From Z G L l last).map k4ViewOf = k4FromSk … (L.map skOf) l last, at all
                  letters.
  `built_sk`      in the goals' scope the 25 segments' skeleton is `skW`: a layers' segment of group
                  g, named "G" ++ toString g, at each even number below 24; no other.

Limits. Equations on plain data; nothing is evaluated here. Nothing on soundness.
-/
import Johnson.Road.K4.K4SentAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (Cut)

/-- `ProofFile.k4Sent`, from the table of steps and the entries. -/
def sentListOn (cuts : List Cut) (es : List Fmt.Entry) (link : String) :
    Option (List (Nat × Nat)) :=
  if cuts.any fun c => c.look == link ++ ".0.call" then
    some ((List.range (rootsOf ((es.drop (beforeAt cuts (link ++ ".0.call"))).take
      (takeAt cuts link)))).map
        fun i => (1, rootsOf (es.take (beforeAt cuts (link ++ ".0.call"))) + i))
  else none

/-- **`ProofFile.k4Sent` is its twin**, at every public part and every name. -/
theorem k4Sent_eq (Z : ProofFile.Pub) (link : String) :
    ProofFile.k4Sent Z link = sentListOn Z.cuts (Z.D.1.map (·.entry)) link := by
  unfold ProofFile.k4Sent ProofFile.Pub.roundsBefore? sentListOn
  by_cases h : (Z.cuts.any fun c => c.look == link ++ ".0.call") = true
  · rw [if_pos h, if_pos h]
    simp only [Option.map_some, k4Roots_eq, List.map_take, List.map_drop]
    all_goals rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- The plain fields of a pair of K4's lot: the Bool · name · link · piece · `before` · group. -/
def k4ViewOf (x : Bool × Par) : Bool × String × Nat × Nat × List (Nat × Nat) × Nat :=
  (x.1, x.2.name, x.2.link, x.2.piece, x.2.before, x.2.g)

/-- What `k4From` reads of a segment: of a layers' segment its group and name; of another
nothing. -/
def skOf (X : LinkH) : Option (Nat × String) := if X.kind == 0 then some (X.g, X.name) else none

/-- `k4From`'s plain fields, from the table of steps, the entries, the number of groups that have a
plan, and the segments' skeleton. -/
def k4FromSk (cuts : List Cut) (es : List Fmt.Entry) (nG : Nat) :
    List (Option (Nat × String)) → Nat → Option String →
      List (Bool × String × Nat × Nat × List (Nat × Nat) × Nat)
  | [], _, _ => []
  | none :: rest, l, last => k4FromSk cuts es nG rest (l + 1) last
  | some (g, name) :: rest, l, last =>
    (if g < nG then
      [(((sentListOn cuts es name).any fun m => !m.isEmpty) &&
          (last.all fun _ => (last.elim (some []) (sentListOn cuts es)).any fun m => !m.isEmpty),
        s!"{name}:3", l, 3,
        (sentListOn cuts es name).getD [] ++ (last.elim (some []) (sentListOn cuts es)).getD [], g)]
    else []) ++ k4FromSk cuts es nG rest (l + 1) (some name)

/-- **What `k4From` lays, in its plain fields, is the twin's value**, at all letters. -/
theorem k4From_view (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ (L : List LinkH) (l : ℕ) (last : Option String),
      (ProofFile.k4From Z G L l last).map k4ViewOf =
        k4FromSk Z.cuts (Z.D.1.map (·.entry)) G.W.G.size (L.map skOf) l last
  | [], _, _ => rfl
  | X :: rest, l, last => by
    have hf : ProofFile.k4Sent Z = sentListOn Z.cuts (Z.D.1.map (·.entry)) := funext (k4Sent_eq Z)
    unfold ProofFile.k4From
    rw [List.map_cons]
    by_cases hk : (X.kind == 0) = true
    · have hs : skOf X = some (X.g, X.name) := by
        unfold skOf
        rw [if_pos hk]
      rw [if_pos hk, hs, List.map_append, k4From_view Z G rest (l + 1) (some X.name), hf]
      show _ = (if X.g < G.W.G.size then _ else _) ++
        k4FromSk Z.cuts (Z.D.1.map (·.entry)) G.W.G.size (rest.map skOf) (l + 1) (some X.name)
      congr 1
      by_cases hg : X.g < G.W.G.size
      · rw [if_pos hg, Array.getElem?_eq_getElem hg]
        rfl
      · rw [if_neg hg, Array.getElem?_eq_none (Nat.le_of_not_lt hg)]
        rfl
    · have hs : skOf X = none := by
        unfold skOf
        rw [if_neg hk]
      rw [if_neg hk, hs, k4From_view Z G rest (l + 1) last]
      rfl

/-- The 25 segments' skeleton in the goals' scope. -/
def skW : List (Option (Nat × String)) :=
  (List.range 25).map fun i =>
    if i % 2 == 0 && i != 24 then some (i / 2, "G" ++ toString (i / 2)) else none

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **In the goals' scope the segments' skeleton is `skW`.** -/
theorem built_sk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) : G₀.built.toList.map skOf = skW := by
  obtain ⟨sz, -⟩ := IM.ground_gets hS hR hZ hG
  obtain ⟨nam, l24, e24, k24, -⟩ := IM.ground_named hS hR hZ hG
  apply List.ext_getElem?
  intro i
  unfold skW
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList]
  by_cases hi : i < 25
  · rw [List.getElem?_range hi]
    by_cases h24 : i = 24
    · subst h24
      rw [e24]
      show some (skOf l24) = some none
      unfold skOf
      rw [k24]
      rfl
    · obtain ⟨l, l', a, ka, ga, Na, b, kb, gb, Nb⟩ := nam (i / 2) (by omega)
      by_cases he : i % 2 = 0
      · have ej : 2 * (i / 2) = i := by omega
        rw [ej] at a
        rw [a]
        show some (skOf l) = some _
        unfold skOf
        rw [ka, ga, Na.name]
        simp [he, h24]
      · have ej : 2 * (i / 2) + 1 = i := by omega
        rw [ej] at b
        rw [b]
        show some (skOf l') = some _
        unfold skOf
        rw [kb]
        simp [he]
  · simp [Array.getElem?_eq_none (show G₀.built.size ≤ i by omega),
      List.getElem?_eq_none (show (List.range 25).length ≤ i by simp; omega)]

#print axioms OnBytes.Road.K4.k4Sent_eq
#print axioms OnBytes.Road.K4.k4From_view
#print axioms OnBytes.Road.K4.built_sk

end OnBytes.Road.K4
