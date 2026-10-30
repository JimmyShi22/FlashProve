-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/JoinFromKeys.lean: CONDITIONAL: the lookup's half of the join
(`JoinMeets`, Johnson/Desc/K5/Honest/Law/Join.lean) from the sentence "keys at points" of the
lookup's row out (`K3Keys`, Johnson/Top/H/K3RowOut.lean), which the table's item on the worth of the
keys says at all rounds for which what the lookup left stands. A joining of the library's lemmas,
each of them an equation; the one step of algebra is a change of sign, in `cEnd_later`. Statements
with their proofs.

The road. "Keys at points" says that the lookup's claim "the join", at each call's key vector at its
point, is 0. That claim is the library's left side of the join at the letters made of the lookup's
own end values (`claimJoin_joinVal`, Johnson/Top/H/K3JoinVal.lean). Where what the lookup left
stands for the rounds, these letters are those read off it (`joinPub_is`,
Johnson/Desc/First/Att/K05KeysAt.lean), and the typed end of the key side is worth what the form
that the lookup left is worth in the world of the ledger (`cEnd_is`, the same file; here at every
later ledger: `cEnd_later`). A tool for the premise hW: a form that names no entry of an array has
one worth in two worlds with the same slots (`value_noEnts`).

Main names:
  `value_noEnts`    a form without entries has one worth in two worlds with the same slots
  `cEnd_later`      the typed end of the key side against the form that the lookup left, in the
                    world of a later ledger
  `keysAt_ext`      each call's key vector at its point is the library's extension of that vector
                    at the call's key point
  `joinMeets_of_keys`   **`JoinMeets` at the values kv**
  `joinMeets_of_worth`   **the same from the table's item on the worth of the keys** and what the
                    lookup leaves

THE PREMISES OF `joinMeets_of_keys`: H, nc, hsh: public: a test on the lookup's shape; four calls;
what the lookup left bears that shape. hI: what the lookup left stands for the rounds rs. hL: G is
later than the ledger that the lookup left. hKeys: "keys at points" at rs. hν: the places' values at
the masks that the form names are the mask row's. hW: the form that the lookup left has one worth in
the world W and in the ledger G's own world at that mask row (so where W has that world's slots:
`value_noEnts`). hkv: each call's key vector at its point is kv c.
Limits. None of the premises is shown to be met here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05KeysAt
import Johnson.Top.H.K3RowOut
import Johnson.Top.H.K3Worth
import Johnson.Desc.First.Att.K05LeftSeats
import Johnson.Desc.K5.Honest.Law.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.OnPublicFiles (K3Keys keysAt)

/-- A form that names no entry of an array has one worth in two worlds with the same slots. -/
theorem value_noEnts {K : Type} [CommRing K] (ρ : Reading K) {f : Aff} (he : f.ents = #[])
    {W W' : World K} (hs : ∀ j, W.slot j = W'.slot j) : f.value ρ W = f.value ρ W' := by
  unfold Aff.value
  rw [he]
  have e : f.slots.toList.map (slotValue ρ W) = f.slots.toList.map (slotValue ρ W') :=
    List.map_congr_left fun x _ => by
      unfold slotValue
      rw [hs]
  rw [e]
  rfl

section
variable {h : Forest.Shape} (lm jLK : ℕ) (rs : TwV.Rounds Cb.Gl.E) {gL : Forest.Heard} {F' : Fork}
  (hI : Fo.HeardIs Reading.gl gL F' (Fo.endsOf h lm jLK rs))
include hI

/-- **The typed end of the key side is worth what the form that the lookup left is worth, in the
world of every later ledger.** The library's `cEnd_is` with a later ledger in the place of the
lookup's own. -/
theorem cEnd_later {G : Fork} (hL : Fo.Later F' G) (ν : Fo.Pl → Cb.Gl.E) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hν : ∀ pc ∈ (Fo.endsOf h lm jLK rs).cEndInc, ν pc.1 = Fo.muOf mask pc.1) :
    Fo.AffK.val ((Fo.endsOf h lm jLK rs).cEndF, (Fo.endsOf h lm jLK rs).cEndC) ν =
      gL.cEnd.value Reading.gl (G.worldOf Reading.gl mask entry) := by
  rw [((hI.cEnd G hL).2 mask entry)]
  have eF : (Fo.endsOf h lm jLK rs).cEndF = TwV.scale (-1) (Fo.endsOf h lm jLK rs).cEndInc := rfl
  have b : Fo.evalL ν (Fo.endsOf h lm jLK rs).cEndInc =
      Fo.evalL (Fo.muOf mask) (Fo.endsOf h lm jLK rs).cEndInc := by
    unfold Fo.evalL
    exact congrArg List.sum (List.map_congr_left fun pc hpc => congrArg (pc.2 * ·) (hν pc hpc))
  show Fo.evalL ν (Fo.endsOf h lm jLK rs).cEndF + (Fo.endsOf h lm jLK rs).cEndC = _
  rw [eF, Fo.evalL_scale, b]
  ring

/-- **Each call's key vector at its point is the library's extension of that vector at the call's
key point.** Conditional: what the lookup left stands for the rounds; its key points, read, are the
library's at z. -/
theorem keysAt_ext {C : Inst.Model.AttSeg.Calls} {z : ℕ → Cb.Gl.E}
    (Kp : VerifiableInference.Desc.First.Att.P.KeyPtsAre Reading.gl C z gL.zk)
    (Kv : ℕ → ℕ → Cb.Gl.E) (c : Fin 4) :
    keysAt h lm jLK Kv rs c.val = Blocks.ext (C.a c) (Kv c.val) (C.zC c z) := by
  have e1 : (Fo.endsOf h lm jLK rs).zk.getD c.val [] =
      Fo.rdA Reading.gl (gL.zk.getD c.val #[]) := by
    rw [← hI.zk, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
      Array.getD_eq_getD_getElem?]
    cases gL.zk[c.val]? <;> rfl
  have e2 : Fo.rdA Reading.gl (gL.zk.getD c.val #[]) =
      (List.range (C.a c)).map (C.zC c z) := by
    refine List.ext_getElem? fun i => ?_
    unfold Fo.rdA
    rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList]
    by_cases hi : i < C.a c
    · have hs : i < (gL.zk.getD c.val #[]).size := by
        rw [Kp.size c]
        exact hi
      rw [Array.getElem?_eq_getElem hs, List.getElem?_range hi]
      show some (Reading.gl.val (gL.zk.getD c.val #[])[i]) = some (C.zC c z i)
      have ga : ∀ (arr : Array E) (ha : i < arr.size), arr.getD i zeroE = arr[i] := fun arr ha => by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ha]
        rfl
      rw [← Kp.read c i hi, ga _ hs]
    · have hs : (gL.zk.getD c.val #[]).size ≤ i := by
        rw [Kp.size c]
        exact Nat.le_of_not_lt hi
      rw [Array.getElem?_eq_none hs, List.getElem?_eq_none (by
        rw [List.length_range]
        exact Nat.le_of_not_lt hi)]
      rfl
  unfold keysAt
  rw [e1, e2, Fo.ext_top]

/-- **The lookup's half of the join, from "keys at points".** Conditional; the premises are listed
in the file's head. -/
theorem joinMeets_of_keys (H : FoNums.ok h = true) (nc : h.NC = 4) (hsh : gL.shape = h) {G : Fork}
    (hL : Fo.Later F' G) (ν : Fo.Pl → Cb.Gl.E) (Kv : ℕ → ℕ → Cb.Gl.E)
    (hKeys : K3Keys h lm jLK ν Kv rs) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hν : ∀ pc ∈ (Fo.endsOf h lm jLK rs).cEndInc, ν pc.1 = Fo.muOf mask pc.1)
    {W : World Cb.Gl.E}
    (hW : gL.cEnd.value Reading.gl W = gL.cEnd.value Reading.gl (G.worldOf Reading.gl mask entry))
    {kv : Fin 4 → Cb.Gl.E} (hkv : ∀ c : Fin 4, keysAt h lm jLK Kv rs c.val = kv c) :
    JoinMeets Reading.gl W gL kv := by
  unfold JoinMeets
  rw [hW, ← cEnd_later lm jLK rs hI hL ν mask entry hν,
    ← VerifiableInference.Desc.First.Att.P.joinPub_is H lm jLK rs hI nc hsh,
    ← show (fun c : Fin 4 => keysAt h lm jLK Kv rs c.val) = kv from funext hkv,
    ← Fo.claimJoin_joinVal h lm jLK rs ν (keysAt h lm jLK Kv rs) nc]
  exact hKeys

end

/-- **The lookup's half of the join, from the table's item on the worth of the keys in front of the
block.** hl: what the lookup leaves, as the library's law on the runs' returns asks it: it holds
rounds for which what the lookup left stands. hItem: the item, at the witness w. kvec: the calls'
vectors of looked-up values in the caller's own letters. Conditional; beside these two: H, nc:
public; hL: G is later than the ledger in front; hν: the item's places at the lookup's masks are the
mask row; hW: the form that the lookup left has one worth in W and in G's own world at that mask
row; Kp: the key points that the lookup left, read, are the library's at z; hKv: the item's vectors
are kvec. -/
theorem joinMeets_of_worth {S₀ Wt St₀ J₀ : Type} [DecidableEq J₀] {fork : S₀ → Option Fork}
    {heard : S₀ → Option Forest.Heard} {fs : Forest.Shape} {lm first : ℕ}
    {ι : Fo.Pl → Option J₀} {Q : Fork → Prop}
    {x0 : Cb.LdLkp.TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)} {gL : Forest.Heard} {s : S₀}
    (hl : VerifiableInference.Desc.First.Att.P.K3LeftOutIs fork heard fs lm first ι Q x0 gL s)
    (nu : Wt → Fo.Pl → Cb.Gl.E) (Kv : Wt → ℕ → ℕ → Cb.Gl.E) (w : Wt)
    (hItem : VerifiableInference.OnPublicFiles.K3WorthKeys fork heard fs lm first nu Kv s w)
    (H : FoNums.ok fs = true) (nc : fs.NC = 4) {G : Fork}
    (hL : ∀ F', fork s = some F' → Fo.Later F' G) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hν : ∀ j, j < first + FoNums.nMasks fs → nu w (.mask j) = mask j) {W : World Cb.Gl.E}
    (hW : gL.cEnd.value Reading.gl W = gL.cEnd.value Reading.gl (G.worldOf Reading.gl mask entry))
    {C : Inst.Model.AttSeg.Calls} {z : ℕ → Cb.Gl.E}
    (Kp : VerifiableInference.Desc.First.Att.P.KeyPtsAre Reading.gl C z gL.zk)
    {kvec : Fin 4 → ℕ → Cb.Gl.E} (hKv : ∀ c : Fin 4, ∀ X < 2 ^ C.a c, Kv w c.val X = kvec c X) :
    JoinMeets Reading.gl W gL fun c => Blocks.ext (C.a c) (kvec c) (C.zC c z) := by
  obtain ⟨F, F', rs, _, hnx, Lf, hh, hf, _⟩ := hl
  have hI := Lf.heardIs
  rw [hnx] at hI
  refine joinMeets_of_keys lm first rs hI H nc Lf.shape (hL F' hf) (nu w) (Kv w)
    (hItem gL F' hf hh rs hI) mask entry (fun pc hpc => ?_) hW fun c => ?_
  · obtain ⟨j, hj, _, h2⟩ := Fo.Slots.onMasksIn_keyTop fs lm first rs pc hpc
    rw [hj]
    exact hν j h2
  · rw [keysAt_ext lm first rs hI Kp]
    exact Blocks.ext_congr (hKv c) _

end H2K5.Honest

#print axioms H2K5.Honest.value_noEnts
#print axioms H2K5.Honest.cEnd_later
#print axioms H2K5.Honest.keysAt_ext
#print axioms H2K5.Honest.joinMeets_of_keys
#print axioms H2K5.Honest.joinMeets_of_worth
