-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/LevelLaw.lean: a layer of a product tree, round by round, over `Fl.levelIn`
(OnBytes/K/Kc/Flat.lean), with everything read off the tape by functions. Statement and proof.

It joins three things: where the function returns, which record it leaves, what it does to the
ledger and what the tape was (FlTape.lean: `levelIn_tape`); the masked sumcheck's law at a product
of two extensions (PscProducts.lean: `products_sound`); and the ledger's own laws on plain records.

`level_law`. FIXED FIRST: the layer's numbers (mu, the point rho, the order of the variables); two
tables A, B over the variables in the order of the rounds; all mask entries; the entries of the
reads; the ledger F in front (its arrays of the right sizes); the claimed form C. THEN there are:
for each mu0 at most one bad eps; for each round fewer than three bad challenges; such that,
wherever the function returns on a tape t: for every later ledger H, in the world in which the
hidden value under slot j is what H shows less its factor times the mask entry: if the layer's row
is 0, the two hidden end values are the tables' extensions at the challenges, and no bad element
was drawn, then C's value (in the world of F) is the sum over the cube, under the equality weights
of rho, of A b * B b.

There is no "there is" behind the return. `tapeMu t` is the first element that the tape's first
round sent, `tapeEps t` the first element that it drew, and `msOf ws (t.drop 1)` (FlTape.lean)
reads the sumcheck's rounds off the rounds behind the first. So a caller who holds a tape can state
each condition of it. The law also says what is left of the tape (all but its first mu + 4 rounds)
and that the layer's tau is what the last of these rounds drew.

A test of the statement: a cheap choice of the sets. With {0} as the set of bad eps and no bad
challenge, one would have to show, for EVERY tape on which the function returns and whose first
round drew an element that does not read as 0: if the row is 0 and the two end values are the
tables' extensions, then C's value is the sum. The tape is under "for all", so nothing can be named
in place of what it drew. And the tape's drawn elements are free: for a C whose value is not the
sum, a tape in which a round's polynomial is not the true one, and in which that round's drawn
element is a place where the two agree, meets the other conditions. Such a tape is shut out only by
a set of bad challenges that holds that place. This is an argument in words: that no other cheap
choice fills the type is not a theorem here.

What is not shown. One direction: from a return. That the tables A and B, the mask and the entries
were fixed before the tape's elements were drawn is the order of the letters, not time; to tie them
to what a prover has committed is the caller's. THE ENTRIES OF THE READS STAND IN FRONT OF THE SETS,
and the sets do read them, through C's value in the world of F: that is right only where C names
nothing that is committed later than this sumcheck's draws (a form in slots alone names no entry).
That the conditions can be met (an honest run) is not shown. The challenges are in the order of the
rounds; L.r has them by places. Counts, no probabilities.
-/
import OnBytes.Desc.First.P1.LevelKit
import OnBytes.Desc.First.P1.FlTape

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc Polynomial
open OnBytes.PscRun (Sized Filled hideRun_ok)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### What is read off a tape -/

/-- The first element that the tape's first round has to send; 0 if there is none. -/
def tapeMu (t : Tape) : E := (t.head?.map fun r => r.sent.headD zeroE).getD zeroE

/-- The first element that the tape's first round drew; 0 if there is none. -/
def tapeEps (t : Tape) : E := (t.head?.map fun r => r.drawn.headD zeroE).getD zeroE

theorem tapeMu_cons (nm : Option String) (z w : Nat) (m : E) (s d : List E) (u : Tape) :
    tapeMu (⟨nm, z, w, m :: s, d⟩ :: u) = m := rfl

theorem tapeEps_cons (nm : Option String) (z w : Nat) (s : List E) (e : E) (d : List E)
    (u : Tape) : tapeEps (⟨nm, z, w, s, e :: d⟩ :: u) = e := rfl

theorem drop_one_cons {α : Type} (r : α) (l : List α) : (r :: l).drop 1 = l := rfl

theorem drop_length_add {α : Type} : ∀ (a b : List α) (k : Nat),
    (a ++ b).drop (a.length + k) = b.drop k
  | [], b, k => by simp
  | x :: a, b, k => by
    have e : (x :: a).length + k = (a.length + k) + 1 := by
      rw [List.length_cons]
      omega
    rw [e, List.cons_append, List.drop_succ_cons]
    exact drop_length_add a b k

theorem drop_cons_append {α : Type} (r0 : α) (rs more : List α) (k : Nat) :
    (r0 :: (rs ++ more)).drop (rs.length + k + 1) = more.drop k := by
  rw [List.drop_succ_cons]
  exact drop_length_add rs more k

theorem drop_level {α : Type} (r0 : α) (rs : List α) (a b c : α) (u : List α) :
    (r0 :: (rs ++ a :: b :: c :: u)).drop (rs.length + 4) = u :=
  drop_cons_append r0 rs (a :: b :: c :: u) 3

theorem drop_level' {α : Type} (r0 : α) (rs : List α) (a b c : α) (u : List α) :
    (r0 :: (rs ++ a :: b :: c :: u)).drop (rs.length + 3) = c :: u :=
  drop_cons_append r0 rs (a :: b :: c :: u) 2

/-! ### The law -/

/-- **A layer of a product tree, over `Fl.levelIn`, read off the tape.** -/
theorem level_law (mu : Nat) (rho : Array E) (order : List Nat) (A B : List Bool → K)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (F : Fork) (hF : Sized F) (C : Aff) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ m0, (badE m0).card ≤ 1) ∧
      (∀ m0 eps pre g, (bad m0 eps pre g).card <
        dAt ((levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]).map (wtOf ρ)) pre.length) ∧
      ∀ (t u : Tape) (L : Level) (G : Fork), Fl.levelIn mu rho C order F t = some (L, G, u) →
        u = t.drop (mu + 4) ∧
        L.r = levelR mu order ((msOf (levelWs mu rho order) (t.drop 1)).map (·.2.2))
          (Array.replicate mu zeroE) ∧
        L.tau = tapeEps (t.drop (mu + 3)) ∧
        Fo.Later F G ∧ Sized G ∧
        ∀ H : Fork, Fo.Later G H →
          L.row.value ρ (H.worldOf ρ mask entry) = 0 →
          (H.worldOf ρ mask entry).slot L.sL =
            mle mu A ((msOf (levelWs mu rho order) (t.drop 1)).map fun m => ρ.val m.2.2) →
          (H.worldOf ρ mask entry).slot L.sR =
            mle mu B ((msOf (levelWs mu rho order) (t.drop 1)).map fun m => ρ.val m.2.2) →
          ρ.val (tapeEps t) ∉ badE (ρ.val (tapeMu t)) →
          (haveI := Classical.decEq K
           NoBad (bad (ρ.val (tapeMu t)) (ρ.val (tapeEps t)))
            (movesP ρ (msOf (levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]) (t.drop 1))
              (addE (tapeMu t) (mulE (tapeEps t) ((F.publicPart C).getD zeroE))))) →
          C.value ρ (F.worldOf ρ mask entry) =
            tot (levelXs ρ mu rho order) fun b => A b * B b := by
  obtain ⟨badE, bad, hE, hB, hrun⟩ := products_sound ρ (levelWs mu rho order)
    (held_level mu rho order) (levelXs ρ mu rho order) (twos_level ρ mu rho order)
    (fun i => if i = 0 then A else B) (fun i => mask (F.next + 1 + 2 * mu + 2 + i)) [(1, 0, 1)]
    (fun i => mask (F.next + i)) (ρ.val ((F.publicPart C).getD zeroE))
    (C.value ρ (F.worldOf ρ mask entry)) (held_atZero 3 (by omega))
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro t u L G h
  obtain ⟨hom, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, ht,
    hrs, _, _, htau, hms, hyy, _, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, htar, heps, hstart,
    hfirst, hrow, hLr, hsL, hsR, hv2, hG1, hshL, hshR, hG⟩ := levelIn_tape h
  -- what the functions read off the tape
  have hwr : (levelWs mu rho order).length = rs.length := by
    rw [levelWs, List.length_map, hom, hrs]
  have q1 : msOf (levelWs mu rho order) (t.drop 1) = ms := by
    rw [ht, drop_one_cons, msOf_append_same _ _ _ hwr, hms]
  have q2 : msOf (levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]) (t.drop 1) =
      ms ++ [y] := by
    rw [ht, drop_one_cons, msOf_append_lit _ _ _ _ _ _ _ _ _ hwr, hms, hyy]
  have q3 : tapeMu t = mu0 := by rw [ht, tapeMu_cons]
  have q4 : tapeEps t = eps := by rw [ht, tapeEps_cons]
  have q5 : (F.publicPart C).getD zeroE = T := by rw [hT, Option.getD_some]
  have hu : u = t.drop (mu + 4) := by rw [ht, ← hrs, drop_level]
  have htau' : L.tau = tapeEps (t.drop (mu + 3)) := by
    rw [htau, ht, ← hrs, drop_level', tapeEps_cons]
  rw [q1, q2, q3, q4, q5]
  -- the ledgers, one later than the other
  have hF' : Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) := hF
  have l0 : Fo.Later F ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) :=
    ⟨by show F.next ≤ F.next + 1 + 2 * mu + 2 + 2; omega, rfl, fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨_, hS1, hin1, _⟩ := hideRun_ok _ G1 L.sL v y.2.2 hF' hG1
  have l1 := Fo.hideRun_later hF' hG1
  obtain ⟨_, hS2, hin2, _⟩ := hideRun_ok G1 G p.first _ _ hS1 hG
  have l2 := Fo.hideRun_later hS1 hG
  refine ⟨hu, hLr, htau', (l0.trans l1).trans l2, hS2, ?_⟩
  intro H lH hzero heL heR hne hnb
  have hlen : (levelWs mu rho order).length = mu := by
    rw [levelWs, List.length_map, hom]
  -- what was shown for the two end values
  have k0 := hin1 0 (by omega)
  have k1 := hin1 1 (by omega)
  rw [Nat.add_zero] at k0
  have f0 := (lH.keep L.sL (l2.keep L.sL k0.2.2.1).1)
  have f1 := (lH.keep (L.sL + 1) (l2.keep (L.sL + 1) k1.2.2.1).1)
  have g0 := l2.keep L.sL k0.2.2.1
  have g1 := l2.keep (L.sL + 1) k1.2.2.1
  have sL' : ρ.val shL = mle mu A (ms.map fun m => ρ.val m.2.2) + ρ.val y.2.2 * mask L.sL := by
    rw [← heL, slot_worldOf, f0.2.1, g0.2.1, f0.2.2, g0.2.2, k0.2.2.2.2, (shown_some hshL).2.2]
    ring
  have sR' : ρ.val shR =
      mle mu B (ms.map fun m => ρ.val m.2.2) + ρ.val y.2.2 * mask (L.sL + 1) := by
    rw [← heR, hsR, slot_worldOf, f1.2.1, g1.2.1, f1.2.2, g1.2.2, k1.2.2.2.2,
      (shown_some hshR).2.2]
    ring
  -- the hiding coefficients
  have hzipl : p.vars.toList.zip p.r.toList = (ms ++ [y]).map fun m => (m.1, m.2.2) := by
    have hv' : p.vars.toList = (ms ++ [y]).map (·.1) := by
      rw [hvars, List.map_append, a1]
      simp [hy]
    rw [hv', hr]
    exact zip_maps _ _ _
  have hwl : p.walk.1.length =
      OnBytes.Psc.hidingEntries (levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]) := by
    rw [Psc.walk, zipT_eq, hidingWalk_length _ (by rw [hzipl]; simp) (by
      intro x hx
      rw [hzipl] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      have := (hheld m hm).spec.1
      show 1 ≤ m.1.d
      omega), hzipl, List.map_map, ← hvars]
    have hv' : p.vars.toList = (ms ++ [y]).map (·.1) := by
      rw [hvars, List.map_append, a1]
      simp [hy]
    rw [hv']
    rfl
  have hslots : ∀ i, i < OnBytes.Psc.hidingEntries
      (levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]) →
      (H.worldOf ρ mask entry).slot (p.first + i) = mask (F.next + i) := by
    intro i hi
    have q := hin2 i (by rw [Array.size_replicate, hwl]; exact hi)
    have r := lH.keep (p.first + i) q.2.2.1
    rw [slot_worldOf, r.2.1, r.2.2, q.2.2.2.1, q.2.2.2.2, hfirst]
    have hz : (Array.replicate p.walk.1.length zeroE).getD i zeroE = zeroE := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [hz, ρ.zero, ρ.sub, ρ.zero, ρ.one]
    ring
  have hCv : p.start.value ρ (H.worldOf ρ mask entry) = C.value ρ (F.worldOf ρ mask entry) := by
    rw [hstart]
    exact Fo.value_later ρ (((l0.trans l1).trans l2).trans lH) C (filledA_of_publicPart hT) mask
      entry
  have hfin := hrun (H.worldOf ρ mask entry) p mu0 ms y (mulE shL shR)
    (fun i => mle (levelWs mu rho order).length ((fun i => if i = 0 then A else B) i)
      (ms.map fun x => ρ.val x.2.2) + ρ.val y.2.2 * mask (F.next + 1 + 2 * mu + 2 + i))
    a1 hy hlens hvars hr (by rw [hclaim, heps, htar]) (by rw [htar, hT]; rfl) hCv hslots
    (by rw [← hrow]; exact hzero) ?_ (fun _ => rfl) (by rw [heps]; exact hne)
    (by rw [heps, htar]; exact hnb)
  · rw [hfin]
    congr 1
    funext b
    simp [sumTerms]
  · rw [ρ.mul, sL', sR', hlen, hsL]
    simp [sumTerms]

end OnBytes.Desc.First.P1
