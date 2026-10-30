-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/SeedJoint.lean: the code switch: THE SAMPLE ROWS THAT THE RECORD
BEHIND HOLDS ARE THE LIBRARY's ROWS AT THE TYPED JOINT SEED's CUT FOR EACH MEMBER.

K2Hears/SeedBehind.lean's seed_behind: the stored sample row of a new message, read as a linear
form, is the library's portZ matrix at (the first bitsZ of round 1's drawn elements, the factor
behind the joint point). The typed sending (Johnson/Pack/PortS.lean's seedsOf cs l) draws ONE joint
seed: bMax coordinates and a factor; a member's seed is its first bitsZ coordinates with the factor
(seedsOf_sd). Here the two meet.
  Tied         the typed list l against the sending's notices: member number i of l is notice number
               i, has one answer and a shape in CaseE or CaseF (see K2Hears/SeedBehind.lean's head)
  JointIs      the typed joint seed is round 1's drawn elements, read: coordinate t is element
               number t, the factor is element number bMax; and there are just bMax + 1 elements
               (then the program's seeds are ONE seed of bMax coordinates: shown inside
               seedIs_joint's proof)
  foldr_max_le  a tool on lists
  seedIs_joint  at a yes: for every member i of l: formsAt at the record behind is the member's
               sample matrix at (seedsOf cs l).sd i sd, for ANY joint seed sd with JointIs. That the
               typed statement behind holds this sd is not said here: no typed statement occurs in
               this file. BY READING this is the text of SeedIs (Johnson/Desc/Sound/Seed.lean) with
               formsAt for its letter forms: the file does not import Seed.lean, and no Lean line
               lays formsAt into SeedIs
  seedIs_sig   the same in the signature's own letters ((sigOf cs l).om i).Z
LIMITS. Tied and JointIs are premises; no lemma of this folder gives them. l MUST COVER EVERY NOTICE
THAT HAS AN ANSWER: the program's seeds have the largest cube's coordinates over ALL sampled notices
of the sending; Tied speaks of notices number 0 to l.length - 1 alone. If a later notice has an
answer and a larger cube, round 1 draws more than bMax + 1 elements, JointIs.len fails at every yes,
and the theorem is idle there. Nothing on the answers. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.SeedBehind
import Johnson.Pack.PortS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Johnson.Pack
open _root_.Tw.K2 (switchNotices)

/-- The typed list against the notices. -/
def Tied (l : List (OracleShape × ℕ)) (notices : Array OracleNotice) : Prop :=
  ∀ i : Fin l.length, ∃ n, notices[i.val]? = some n ∧ n.shape = (l.get i).1 ∧
    n.shape.answers = 1 ∧ (CaseE n.shape ∨ CaseF n.shape)

/-- The typed joint seed is what round 1 drew, read. -/
structure JointIs (cs : Codes) (l : List (OracleShape × ℕ)) (r₁ : Fmt.RoundView)
    (sd : (Fin (bMax cs l) → GE) × GEˣ) : Prop where
  len : r₁.drawn.elems.length = bMax cs l + 1
  point : ∀ t : Fin (bMax cs l), sd.1 t = readL (r₁.drawn.elems.map E.ofTriple) t.val
  factor : (sd.2 : GE) = readL (r₁.drawn.elems.map E.ofTriple) (bMax cs l)

theorem foldr_max_le : ∀ (L : List ℕ) (b : ℕ), (∀ x ∈ L, x ≤ b) → L.foldr max 0 ≤ b
  | [], _, _ => Nat.zero_le _
  | x :: L, b, h => by
    rw [List.foldr_cons]
    exact Nat.max_le.2 ⟨h x (List.mem_cons_self ..),
      foldr_max_le L b fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

/-- **The record behind holds the library's rows at the typed joint seed's cut.** -/
theorem seedIs_joint {p : K2.P2} {s s' : VerifiableInference.Desc.First.S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : K2.AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (l : List (OracleShape × ℕ))
    (T : Tied l (switchNotices x.T x.others))
    (sd : (Fin (bMax x.st.codes l) → GE) × GEˣ) (J : JointIs x.st.codes l r₁ sd)
    (i : Fin l.length) :
    K2.formsAt x.st.codes (l.get i).1 s'.st (x.st.oracles.size + i.val) =
      some ((portZ x.st.codes (l.get i).1).mat ((seedsOf x.st.codes l).sd i sd)) := by
  obtain ⟨bits, answers, seeds, hseeds, hall⟩ := K2.seed_behind A
  have htot := K2.seedsOf_total bits answers _ seeds hseeds
  rw [List.length_map, J.len] at htot
  -- every member's cube is below the program's number of coordinates
  have hle : bMax x.st.codes l ≤ bits := by
    unfold bMax
    refine foldr_max_le _ _ fun v hv => ?_
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
    obtain ⟨k, hk⟩ := List.get_of_mem hz
    obtain ⟨n, hn, hs, h1, hc⟩ := T k
    obtain ⟨b, -, -, h3, -⟩ := hall k.val n hn h1 hc
    rw [← hk, ← hs]
    exact h3
  have hbits : bits = bMax x.st.codes l := by
    rcases Nat.eq_zero_or_pos answers with h0 | h0
    · rw [h0] at htot
      omega
    · have : 1 * (bits + 1) ≤ answers * (bits + 1) := Nat.mul_le_mul_right _ h0
      omega
  obtain ⟨n, hn, hs, h1, hc⟩ := T i
  obtain ⟨b, hb, -, -, hf⟩ := hall i.val n hn h1 hc
  have hβ : (sd.2 : GE) = readE b := by
    rw [J.factor]
    unfold readL
    rw [List.getD_eq_getElem?_getD, ← hbits, hb]
    rfl
  have e := hf sd.2 hβ
  rw [hs] at e
  rw [e]
  congr 2
  obtain ⟨z, β⟩ := sd
  rw [seedsOf_sd]
  refine Prod.ext (funext fun t => ?_) rfl
  exact (J.point (Fin.castLE (bits_le x.st.codes l i) t)).symm

/-- The same in the signature's own letters: by reading, `formsAt … = some (Z.mat ρ)` is the text of
SeedIs (Johnson/Desc/Sound/Seed.lean). -/
theorem seedIs_sig {p : K2.P2} {s s' : VerifiableInference.Desc.First.S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : K2.AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (l : List (OracleShape × ℕ))
    (T : Tied l (switchNotices x.T x.others))
    (sd : (seedsOf x.st.codes l).D) (J : JointIs x.st.codes l r₁ sd) (i : Fin l.length) :
    (K2.formsAt x.st.codes (l.get i).1 s'.st (x.st.oracles.size + i.val) :
        Option (((sigOf x.st.codes l).om i).Z.S → ((sigOf x.st.codes l).om i).C.J → GE)) =
      some (((sigOf x.st.codes l).om i).Z.mat ((seedsOf x.st.codes l).sd i sd)) :=
  seedIs_joint A l T sd J i

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.seedIs_sig
#print axioms VerifiableInference.Desc.First.K2Hands.seedIs_joint
