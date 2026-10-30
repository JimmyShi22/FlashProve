-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TieBehind.lean: THE SMALLNESS TEST: THE TIE's HALF OF `SecondEqs`
(Johnson/Desc/K8/Honest/SecondParts.lean) BEHIND A YES OF THE BATCHING BLOCK, AT WHATEVER CHALLENGE,
FROM PREMISES THAT ALL STAND IN FRONT OF THE BATCHING; SO THE PREMISE ON `SecondEqs` OF
`second_at_link` (Johnson/Desc/K8/Honest/SecondFew.lean) FROM THE PIECES' HALF BEHIND AND THE TIE's
HALF IN FRONT. Definitions and lemmas; none of the library's goals. No prover stands in them;
nothing on completeness, soundness or hiding. An assembly.

  `PlainOffA a nf nb M t r i`, `plainOff_of_a`   no plain claim bears on the entry, in the letter a
      of `Gathers` (Johnson/Desc/K8/Honest/FallCount.lean), which hangs on no challenge; from it
      `PlainOff` (Added8.lean) at the claims of a yes
  `TieOwed tl F funs a nf nb`   what the tie's half asks: `tiesLaid`, `symbolsLaid`, `TieFront`;
      every virtual row begins at column 0; each matrix's array has a virtual row 0; the second
      computation's number of blocks is the data's; `PlainOffA` at the ties' row's digits and at the
      matrices' arrays
  **`tieEqs_behind`**   under `Gathers` and `TieOwed`: behind a yes at the challenge x the state
      holds data and a ledger at which `TieEqs` holds of every matrix
  `PiecesEqs tl F`, `secondEqs_of_halves`   the pieces' half of `SecondEqs`, by name; the two halves
      give the whole
  **`secondEqs_at_link`**   at a plain segment. ITS FIRST STEPS ARE THOSE OF `second_at_link`,
      WRITTEN A SECOND TIME
By: `behind_open` (Added8.lean) · `Added8.tieEqs` (TieWhole.lean) · `k8_cut` (FallReads.lean) ·
`wants_same`, `hasRow_of_shape` (SecondFew.lean) · `gathers_of_plain` (GathersPlain.lean) ·
`funs_of_yes` (FallAtt.lean) · `batch_ok`, `drawnAt_ok`, `tlFork_iff`, `L0_of_shape`,
`shape_of_frame` (FallDraw.lean) · eq_same (Johnson/Desc/First/TailClaims/EquationsCover.lean).
Limits. NOTHING IS SHOWN OF ANY STATE: `TieOwed` and `PiecesEqs` are premises. `TieOwed` is asked at
whatever tables, numbers and letter a meet `Gathers`, where the batching says yes at some challenge.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.TieWhole
import Johnson.Desc.K8.Honest.SecondFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **(i), in front, in the letter of `Gathers`**: no plain claim bears on entry i of virtual row r
of array t: a j t r i is the j-th claim's coefficient there; nf claims stand in front of the list
"K8.equations", whose first four are plain too; M more of the list; nb behind. -/
def PlainOffA (a : Nat → Nat → Nat → Nat → Cb.Gl.E) (nf nb M t r i : Nat) : Prop :=
  (∀ j, j < nf + 4 → a j t r i = 0) ∧ ∀ j, j < nb → a (nf + (4 + M) + j) t r i = 0

/-- From the letter to the claims. -/
theorem plainOff_of_a {a : Nat → Nat → Nat → Nat → Cb.Gl.E} {nf nb M : Nat}
    {fr k8 bk : List Claim} {t r i : Nat} (hnf : fr.length = nf) (h4 : (k8.take 4).length = 4)
    (hk : k8.length = 4 + M) (hnb : bk.length = nb)
    (hA : ∀ c cl, (fr ++ k8.take 4)[c]? = some cl → ∀ t r i, coefOn cl t r i = a c t r i)
    (hB : ∀ c cl, bk[c]? = some cl → ∀ t r i, coefOn cl t r i = a (nf + k8.length + c) t r i)
    (h : PlainOffA a nf nb M t r i) : PlainOff fr k8 bk t r i := by
  refine ⟨fun j cl hj => ?_, fun j cl hj => ?_⟩
  · rw [hA j cl hj]
    refine h.1 j ?_
    have k := (List.getElem?_eq_some_iff.1 hj).1
    rw [List.length_append, hnf, h4] at k
    exact k
  · rw [hB j cl hj, hk]
    refine h.2 j ?_
    have k := (List.getElem?_eq_some_iff.1 hj).1
    rw [hnb] at k
    exact k

/-- **What the tie's half asks, all of it in front of the batching**: no challenge stands in it. -/
structure TieOwed (tl : HTailF2) (F : Fork) (funs : Array HFun)
    (a : Nat → Nat → Nat → Nat → Cb.Gl.E) (nf nb : Nat) : Prop where
  laid : tiesLaid tl = true
  sym : symbolsLaid tl = true
  front : TieFront tl
  zero : ∀ t r, ((F.trees.getD t {}).rows.getD r {}).L0 = 0
  row : ∀ mu, mu < tl.NM → HasRow F (tl.gtTree.getD mu 0) 0
  blocks : ∀ nbW W, tl.wants = some (nbW, W) → nbW = tl.zzBlocks
  offT : ∀ mu, mu < tl.NM → ∀ i, i < (tl.mats.getD mu {}).m → ∀ plane, plane ≤ 1 →
    PlainOffA a nf nb (tl.NM + (readsList tl funs).length) tl.ix.ZZ tl.zzRowTies
      (plane * tl.mz + tl.off.getD mu 0 + i)
  offS : ∀ mu, mu < tl.NM → ∀ c, c < (tl.mats.getD mu {}).k →
    PlainOffA a nf nb (tl.NM + (readsList tl funs).length) (tl.gtTree.getD mu 0) 0 c

/-- **THE TIE's HALF BEHIND A YES OF THE BATCHING BLOCK, AT WHATEVER CHALLENGE.** -/
theorem tieEqs_behind (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hG : Gathers p g s tl funs nf nb a)
    (hO : TieOwed tl F funs a nf nb) (x : Cb.Gl.E) (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧
      ∀ (g₀ : Forest.Heard) (nbW : Nat) (W : List Want), tl'.wants = some (nbW, W) →
        ∀ mu, mu < tl'.NM →
          TieEqs tl' (coefBody tl' g₀ G) (tiesL tl' (coefBody tl' g₀ G) nbW) mu := by
  obtain ⟨tl', Y, G, F₁, F₂, fr, k8, bk, n₀, hget, A, -, -, hsh, hnf, hnb, hA, hB⟩ :=
    behind_open p g batch s t' tl F funs nf nb a hb hs hG x hbt
  obtain ⟨-, -, -, -, h4, hk, -⟩ := k8_cut A.eq
  have eN : tl'.NM = tl.NM :=
    eq_same (·.NM) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eτ : tl'.tau = tl.tau :=
    eq_same (·.tau) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have ez : tl'.mz = tl.mz :=
    eq_same (·.mz) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have shG : shapeOf G.trees = shapeOf F.trees := (shape_of_frame _ _ A.core.2.2.1).trans hsh
  refine ⟨tl', G, hget, fun g₀ nbW W hW mu hmu => ?_⟩
  rw [wants_same eτ ez] at hW
  exact A.tieEqs g₀ nbW (hO.blocks nbW W hW) hO.laid hO.sym hO.front
    (fun t r => by
      rw [L0_of_shape, hsh, ← L0_of_shape]
      exact hO.zero t r)
    (fun nu hnu => hasRow_of_shape shG (hO.row nu hnu))
    (fun nu hnu i hi pl hp => plainOff_of_a hnf h4 hk hnb hA hB (hO.offT nu hnu i hi pl hp))
    (fun nu hnu c hc => plainOff_of_a hnf h4 hk hnb hA hB (hO.offS nu hnu c hc))
    mu (eN ▸ hmu)

/-- **The pieces' half of what must never fail.** -/
def PiecesEqs (tl : HTailF2) (F : Fork) : Prop :=
  ∀ g jo nbW W, tl.heard = some g → tl.joinObj9 = some jo → tl.wants = some (nbW, W) →
    ∀ w ∈ W, PieceEqs tl (coefBody tl g F) g (t2fKappaByText (coefBody tl g F).theta jo) w

/-- The two halves. -/
theorem secondEqs_of_halves {tl : HTailF2} {F : Fork} (h1 : PiecesEqs tl F)
    (h2 : ∀ (g₀ : Forest.Heard) (nbW : Nat) (W : List Want), tl.wants = some (nbW, W) →
      ∀ mu, mu < tl.NM → TieEqs tl (coefBody tl g₀ F) (tiesL tl (coefBody tl g₀ F) nbW) mu) :
    SecondEqs tl F :=
  fun g jo nbW W hg hj hW => ⟨h1 g jo nbW W hg hj hW, h2 g nbW W hW⟩

/-- **AT A PLAIN SEGMENT: `second_at_link`'s premise on `SecondEqs`, from the pieces' half behind
and the tie's half IN FRONT.** -/
theorem secondEqs_at_link (L : Link S Claim) (hL : PlainLink L) (p : K9.Where)
    (batch : S → List Fmt.RoundView → Except String S) (s : S)
    (hb : ∀ rs t, batch s rs = .ok t →
      (K9.batch K9.atS p (claimsInBy L.each L.hear L.order)).decide s rs [] = .ok t)
    (hTie : ∀ tl F funs nf nb a, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
      Gathers p (claimsInBy L.each L.hear L.order) s tl funs nf nb a →
      (∃ x t', batch s [⟨[], chiAt x⟩] = .ok t') → TieOwed tl F funs a nf nb)
    (hPc : ∀ x t' tl' G, batch s [⟨[], chiAt x⟩] = .ok t' → tlForkP.get? t' = some (tl', G) →
      PiecesEqs tl' G) :
    ∀ x t' tl' G, batch s [⟨[], chiAt x⟩] = .ok t' → tlForkP.get? t' = some (tl', G) →
      SecondEqs tl' G := by
  intro x t' tl' G hbt hget
  obtain ⟨i, pre, post, hord, Hpre, Hpost, tEq⟩ := hL
  obtain ⟨t, e, cls, y, G₀, hdr, hg, -, -, -⟩ := batch_ok p _ s t' (chiAt x) (hb _ _ hbt)
  obtain ⟨a0, -, -, ha0, -, -, -⟩ := drawnAt_ok p s t (chiAt x) hdr
  have hF : s.fork? = some a0.F := K9.get_fork s a0 ha0
  obtain ⟨funs, hf⟩ := Option.isSome_iff_exists.1
    (funs_of_yes L p i pre post hord Hpre Hpost tEq s _ t e cls hdr hg)
  obtain ⟨tl, ht⟩ : ∃ tl, s.tl? = some tl := by
    cases h : s.tl? with
    | some tl => exact ⟨tl, rfl⟩
    | none =>
      exfalso
      simp [K9.atS, h] at ha0
  obtain ⟨nf, nb, a, hGa⟩ := gathers_of_plain L p i pre post hord Hpre Hpost tEq s tl funs ht hf
  obtain ⟨tl'', G'', hget', H⟩ := tieEqs_behind p _ batch s t' tl a0.F funs nf nb a hb
    ((tlFork_iff s tl a0.F).2 ⟨ht, hF⟩) hGa (hTie tl a0.F funs nf nb a ht hF hf hGa ⟨x, t', hbt⟩) x
    hbt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hget.symm.trans hget'))
  exact secondEqs_of_halves (hPc x t' tl' G hbt hget) H

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.plainOff_of_a
#print axioms VerifiableInference.Desc.First.K8.Honest.tieEqs_behind
#print axioms VerifiableInference.Desc.First.K8.Honest.secondEqs_of_halves
#print axioms VerifiableInference.Desc.First.K8.Honest.secondEqs_at_link
