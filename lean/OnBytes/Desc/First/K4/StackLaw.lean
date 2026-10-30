-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/StackLaw.lean: THE BATCHED SUMCHECK OF THE LAYERS' OWN ROUNDS, ROUND BY
ROUND, over `hearStack` (OnBytes/Desc/First/K4/Hear.lean) at the plain engine `engFl`, with
everything read off the tape by functions. Statement and proof.

It joins three things: where the function returns, with the tape (StackTape.lean:
`hearStack_tape`); the masked sumcheck's law at two end terms, each under a mask that may depend on
the challenges (OnBytes/Desc/First/P1/PscEnds.lean: `two_ends_sound`); and the ledger's laws
(Heard.lean: `own_slots`, `walk_length`).

  `stackStart`, `stackMs`, `stackY`: the start form that the text makes of the powers of the first
    round's drawn element; the sumcheck's rounds; its round in the further variable: functions of
    the tape.
  `stack_law`. FIXED FIRST: the public record, the caller's environment, what was heard before, the
    two numbers of the plan; two tables A, B over lamS bits, the first bit for the first round; two
    functions ma, mb of the challenges; all mask entries; the ledger F in front (its arrays of the
    right sizes). THEN there are sets of bad elements WITH THE LETTERS T (the start form's value on
    what was shown) AND Cv (its value at the hidden values): for each T, Cv and mu0 at most one bad
    eps; for each round fewer than three bad challenges; such that, wherever the function returns
    on a tape t: for every later ledger Hl and all entries of the reads, in Hl's world: if the row
    is 0, the two end elements read as A's and B's extensions at the challenges plus beta times ma
    and mb, and no bad element was drawn, then the start form's value is the plain sum over the
    cube of A b * B b.

THE COUNT "at most one bad eps for each Cv" SERVES ONLY A CALLER WHO SHOWS THAT Cv IS FIXED IN
FRONT OF eps. The start form names entries of the reads, which a prover commits behind these draws:
a prover who picks the reads behind eps picks Cv, and with it the set.

What is not shown. One direction: from a return. The draw of the first round's element, of whose
powers the start form is made, has no bad set here. That the two conditions on the end elements
hold, and what the tables are, is the caller's. That the letters in front were fixed before the
tape's elements were drawn is the order of the letters, not time. That the conditions can be met
together is not shown. The challenges are in the order of the rounds; K.rs has them reversed.
Counts, no probabilities.
-/
import OnBytes.Desc.First.K4.StackTape
import OnBytes.Desc.First.P1.Heard
import OnBytes.Desc.First.P1.PscEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc Polynomial
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Desc.First.P1 (msOf plainWs endP endP_spec Rnd Held claimAfter movesP NoBad dAt wtOf
  Twos tot mle tapeMu tapeEps tapeMu_cons tapeEps_cons roundAt roundAt_cons own_slots walk_length
  two_ends_sound held_atZero two_plain msOf_append_same drop_one_cons drop_first drop_tsc)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### Small things -/

theorem held_plain3 : Held (OnBytes.Psc.Weight.plain 3) :=
  ⟨(OnBytes.PscRun.fits_plain 3).mpr (by omega), OnBytes.PscRun.weightHeld_plain 3 (by omega)⟩

theorem held_plainWs (n : Nat) : ∀ w ∈ plainWs n, Held w := by
  intro w hw
  rw [List.eq_of_mem_replicate hw]
  exact held_plain3

theorem twos_plainWs : ∀ n : Nat, Twos 3 ((plainWs n).map (wtOf ρ)) (List.replicate n (1, 1))
  | 0 => trivial
  | n + 1 => ⟨two_plain ρ 3 (by omega), le_refl 3, twos_plainWs n⟩

theorem drop_two_cons {α : Type} (a b : α) (l : List α) : (a :: b :: l).drop 2 = l := rfl

theorem drop_succ_cons' {α : Type} (a : α) (l : List α) (n : Nat) :
    (a :: l).drop (n + 1) = l.drop n := rfl

/-! ### What is read off the tape -/

/-- The start form that the text makes of the powers of the first round's drawn element; the empty
form where it makes none. -/
def stackStart (v : Env) (H : Heard) (F : Fork) (t : Tape) : Aff :=
  ((joinStart engFl v H (powers (tapeEps t) 2) F (t.drop 1)).map (·.1)).getD {}

/-- The sumcheck's rounds. -/
def stackMs (lamS : Nat) (t : Tape) : List Rnd := msOf (plainWs lamS) (t.drop 2)

/-- The sumcheck's round in the further variable. -/
def stackY (lamS : Nat) (t : Tape) : Rnd :=
  roundAt (OnBytes.Psc.Weight.atZero 3) (t.drop (lamS + 2))

/-! ### The law -/

/-- **The batched sumcheck, over `hearStack`, read off the tape.** -/
theorem stack_law (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) (A B : List Bool → K)
    (ma mb : List K → K) (mask : ℕ → K) (F : Fork) (hF : Sized F) :
    ∃ (badE : K → K → K → Finset K)
      (bad : K → K → K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ T Cv m0, (badE T Cv m0).card ≤ 1) ∧
      (∀ T Cv m0 eps pre g, (bad T Cv m0 eps pre g).card <
        dAt ((plainWs lamS ++ [OnBytes.Psc.Weight.atZero 3]).map (wtOf ρ)) pre.length) ∧
      ∀ (t u : Tape) (S : HeardStack) (G : Fork),
        hearStack engFl P v H lamS NCLp F t = some (S, G, u) →
        u = t.drop (lamS + 4) ∧
        S.rs.toList = ((stackMs lamS t).map (·.2.2)).reverse ∧
        Fo.Later F G ∧ Sized G ∧
        ∀ (Hl : Fork) (entry : ℕ → ℕ → ℕ → K), Fo.Later G Hl →
          S.rowS.value ρ (Hl.worldOf ρ mask entry) = 0 →
          ρ.val S.fin.As = mle lamS A ((stackMs lamS t).map fun m => ρ.val m.2.2) +
            ρ.val (stackY lamS t).2.2 * ma ((stackMs lamS t).map fun m => ρ.val m.2.2) →
          ρ.val S.fin.Bs = mle lamS B ((stackMs lamS t).map fun m => ρ.val m.2.2) +
            ρ.val (stackY lamS t).2.2 * mb ((stackMs lamS t).map fun m => ρ.val m.2.2) →
          ρ.val (tapeEps (t.drop 1)) ∉
            badE (ρ.val ((F.publicPart (stackStart v H F t)).getD zeroE))
              ((stackStart v H F t).value ρ (Hl.worldOf ρ mask entry))
              (ρ.val (tapeMu (t.drop 1))) →
          (haveI := Classical.decEq K
           NoBad (bad (ρ.val ((F.publicPart (stackStart v H F t)).getD zeroE))
              ((stackStart v H F t).value ρ (Hl.worldOf ρ mask entry))
              (ρ.val (tapeMu (t.drop 1))) (ρ.val (tapeEps (t.drop 1))))
            (movesP ρ (stackMs lamS t ++ [stackY lamS t])
              (addE (tapeMu (t.drop 1)) (mulE (tapeEps (t.drop 1))
                ((F.publicPart (stackStart v H F t)).getD zeroE))))) →
          (stackStart v H F t).value ρ (Hl.worldOf ρ mask entry) =
            tot (List.replicate lamS (1, 1)) fun b => A b * B b := by
  choose badE bad hE hB hrun using fun (T Cv : K) =>
    two_ends_sound ρ (plainWs lamS) (held_plainWs lamS) (List.replicate lamS (1, 1))
      (twos_plainWs ρ lamS) A B ma mb (fun i => mask (F.next + i)) T Cv
      (held_atZero 3 (by omega))
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro t u S G h
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, ht, hrs, _, hC, hT,
    hms, hyy, hp, a1, hheld, hlens, hSrs, hsA0, _, _, _, _, hG1, hrow, hG⟩ := hearStack_tape h
  -- what the functions read off the tape
  have hlen : (plainWs lamS).length = lamS := List.length_replicate
  have hwr : (plainWs lamS).length = rs.length := by rw [hlen, hrs]
  have q0 : tapeEps t = x := by rw [ht, tapeEps_cons]
  have q1 : stackMs lamS t = ms := by
    unfold stackMs
    rw [ht, drop_two_cons, msOf_append_same _ _ _ hwr, hms]
  have q2 : stackY lamS t = y := by
    unfold stackY
    rw [ht, ← hrs, drop_succ_cons', drop_first, roundAt_cons, hyy]
  have q3 : tapeMu (t.drop 1) = mu0 := by rw [ht, drop_one_cons, tapeMu_cons]
  have q4 : tapeEps (t.drop 1) = eps := by rw [ht, drop_one_cons, tapeEps_cons]
  have q5 : stackStart v H F t = C := by
    unfold stackStart
    rw [q0, hC, Option.map_some, Option.getD_some]
  have q6 : (F.publicPart C).getD zeroE = T := by rw [hT, Option.getD_some]
  have hu : u = t.drop (lamS + 4) := by rw [ht, ← hrs, drop_succ_cons', drop_tsc]
  rw [q1, q2, q3, q4, q5, q6]
  -- the ledgers, one later than the other
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } :
      Fork) := hF
  have l0 : Fo.Later F
      ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork) :=
    ⟨by show F.next ≤ F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp); omega, rfl,
      fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨_, hS1, _, _⟩ := hideRun_ok _ G1 S.sA0 vals beta hF' hG1
  have l1 := Fo.hideRun_later hF' hG1
  obtain ⟨l2, hS2, _⟩ := own_slots ρ mask (fun _ _ _ => 0) hS1 hG
  refine ⟨hu, hSrs, (l0.trans l1).trans l2, hS2, ?_⟩
  intro Hl entry lH hzero hAs hBs hne hnb
  -- the record
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := endP_spec
    { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true } ms y
  rw [← hp] at e1 e2 e3 e4 e5 e6 e7
  have hy : y.1 = OnBytes.Psc.Weight.atZero 3 := by rw [hyy]
  have hv' : p.vars.toList = (ms ++ [y]).map (·.1) := e1
  have hvars : p.vars.toList = plainWs lamS ++ [OnBytes.Psc.Weight.atZero 3] := by
    rw [hv', List.map_append, a1, List.map_singleton, hy]
  have hr : p.r.toList = (ms ++ [y]).map (·.2.2) := e2
  have hwl : p.walk.1.length =
      OnBytes.Psc.hidingEntries (plainWs lamS ++ [OnBytes.Psc.Weight.atZero 3]) := by
    rw [walk_length (by simp) hv' hr hheld, ← hv', hvars]
  have hslots : ∀ i, i < OnBytes.Psc.hidingEntries
      (plainWs lamS ++ [OnBytes.Psc.Weight.atZero 3]) →
      (Hl.worldOf ρ mask entry).slot (p.first + i) = mask (F.next + i) := by
    intro i hi
    have e := (own_slots ρ mask entry hS1 hG).2.2 Hl lH i (by rw [hwl]; exact hi)
    have hfirst : p.first = F.next := e7
    rw [hfirst] at e ⊢
    exact e
  have heps : p.eps = eps := e6
  have htar : p.target = T := e5
  have hstart : p.start = C := e4
  have hclaim : p.claim = claimAfter (ms ++ [y]) (addE mu0 (mulE eps T)) := e3
  exact hrun (ρ.val T) (C.value ρ (Hl.worldOf ρ mask entry)) (Hl.worldOf ρ mask entry) p mu0 ms y
    (mulE S.fin.As S.fin.Bs) a1 hy hlens hvars hr (by rw [hclaim, heps, htar]) (by rw [htar])
    (by rw [hstart]) hslots (by rw [← hrow]; exact hzero) (by rw [ρ.mul, hAs, hBs, hlen])
    (by rw [heps]; exact hne) (by rw [heps, htar]; exact hnb)

end OnBytes.Desc.First.K4
