-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KvVec.lean

The key vectors kvA of an attention sub-proof's four lookup calls, a term written for this library
over the verifier's records (OnBytes/Tie/Pv/Lookup/Ends/A.lean), are the library's key vectors of
an attention segment (Inst/Model/Att/Trace.lean: keyVec), at every index that lies in a piece. Two
formulas are tied: kvA and keyVec. The verifier holds no key vector: it evaluates key forms.

Main definitions and theorems:
* "pcAt s l base b": the piece of segment s for pair number b (layer b / HA, query head b % HA), of
  2^l keys, from key number base + b 2^l on.
* "LaidA S cs": HOW THE FOUR CALLS ARE LAID. cs q is call number q of the shape; the pieces of
  each call are pairwise apart; call 0 holds, for every pair b, the piece of rm at b 2^lM and the
  piece of rd behind all of these; call 1 likewise fm and fd, and has the first layer's shift; call
  2 wl and ix; call 3 wh. Numbers and records of the shape alone: public. A premise here; a theorem
  at what the verifier's shapeHid returns at the call list of four lines with one shift
  (laidA_of_hid, Lane5AttLaid.lean); a test with its theorem: Lane5KvCheck.lean; the runs, at two
  typed configurations: Lane5KvWit.lean.
* "kv_fam": a call's key vector at a place of a family of such pieces.
* **"kvA_eq_keyVecC"**: under "NumsA S" and "LaidA S cs", for every field K, EVERY reading cell of
  A.lean's names, every call c and every X below the library's "used c":
  kvA S fs cell c X = keyVec (dimOf S) (tbOf S) (tC S cell) c X.
* "kvA_eq_keyVec": the same at a list Z of integer matrices: cell := cellZ Z, where tC is
  castT (cellsA S Z).

Not claimed: anything at an index behind the pieces (the padding: Lane5KvAll.lean); that a shape is
laid so; that the vector whose extension the verifier's key form evaluates is kvA (that is shown
in OnBytes/Tie/Pv/Lookup/Ends/AlgA.lean, AlgA2.lean, AlgA3.lean and, over the verifier's own forms
and world, AlgAW.lean, under the premise rule of these theorems: each slot of the world that a key
form reads holds the extension of its cells (for the scores and accumulators: of the products) at
the key point).
-/
import Johnson.Road.Lane5KvKey2
import OnBytes.Tie.Pv.Lookup.Ends.AlgA
import Johnson.Road.Ends.PiecesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A
open OnBytes.Attention (Seg ACall)
open Inst.Model.AttSeg

/-- The piece of segment s for pair number b, of 2^l keys, from key number base + b 2^l on. -/
def pcAt (S : Attention.Shape) (s : Seg) (l base b : ℕ) : Pc :=
  { seg := s, lam := b / S.HA, a := b % S.HA, b := l, off := base + b * 2 ^ l }

/-- **How the four calls are laid.** Public. -/
structure LaidA (S : Attention.Shape) (cs : Fin 4 → ACall) : Prop where
  isCall : ∀ q : Fin 4, S.calls[q.val]? = some (cs q)
  ap : ∀ q : Fin 4, (cs q).pcs.toList.Pairwise fun p r =>
    p.off + 2 ^ p.b ≤ r.off ∨ r.off + 2 ^ r.b ≤ p.off
  sh : (cs 1).sh = S.cf.sh.getD 0 0
  rm : ∀ b < (dimOf S).nb, pcAt S .rm (dimOf S).lM 0 b ∈ (cs 0).pcs.toList
  rd : ∀ b < (dimOf S).nb,
    pcAt S .rd (dimOf S).lD ((dimOf S).nb * 2 ^ (dimOf S).lM) b ∈ (cs 0).pcs.toList
  fm : ∀ b < (dimOf S).nb, pcAt S .fm (dimOf S).lM 0 b ∈ (cs 1).pcs.toList
  fd : ∀ b < (dimOf S).nb,
    pcAt S .fd (dimOf S).lD ((dimOf S).nb * 2 ^ (dimOf S).lM) b ∈ (cs 1).pcs.toList
  wl : ∀ b < (dimOf S).nb, pcAt S .wl (dimOf S).lW 0 b ∈ (cs 2).pcs.toList
  ix : ∀ b < (dimOf S).nb,
    pcAt S .ix (dimOf S).lX ((dimOf S).nb * 2 ^ (dimOf S).lW) b ∈ (cs 2).pcs.toList
  wh : ∀ b < (dimOf S).nb, pcAt S .wh (dimOf S).l4 0 b ∈ (cs 3).pcs.toList

variable {K : Type} [Field K] {S : Attention.Shape}

/-- **A call's key vector at a place of a family of pieces.** -/
theorem kv_fam (fs : Model.Forest.Shape) (cell : NameA → K) (q : ℕ) (c : ACall)
    (hc : S.calls[q]? = some c)
    (ap : c.pcs.toList.Pairwise fun p r => p.off + 2 ^ p.b ≤ r.off ∨ r.off + 2 ^ r.b ≤ p.off)
    (s : Seg) (l base nb : ℕ) (hm : ∀ b < nb, pcAt S s l base b ∈ c.pcs.toList) (Y : ℕ)
    (hY : Y < nb * 2 ^ l) :
    kvA S fs cell q (base + Y) =
      segKey S cell c.sh s (Y / 2 ^ l / S.HA) (Y / 2 ^ l % S.HA) (Y % 2 ^ l) := by
  have hb : Y / 2 ^ l < nb := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hY)
  obtain ⟨h1, h2, h3⟩ := block_of Y l
  rw [kvA_eq S fs cell q c hc,
    pwVec_mem (fun p : Pc => p.off) (fun p => p.b) _ _ _ ap (pcAt S s l base (Y / 2 ^ l))
      (hm _ hb) (base + Y)
      ⟨by show base + Y / 2 ^ l * 2 ^ l ≤ base + Y; omega,
        by show base + Y < base + Y / 2 ^ l * 2 ^ l + 2 ^ l; omega⟩]
  show segKey S cell c.sh s (Y / 2 ^ l / S.HA) (Y / 2 ^ l % S.HA)
    (base + Y - (base + Y / 2 ^ l * 2 ^ l)) = _
  rw [show base + Y - (base + Y / 2 ^ l * 2 ^ l) = Y % 2 ^ l by omega]

/-- The first family of twoFam. -/
theorem twoFam_fst (nb l l' : ℕ) (f f' : ℕ → ℕ → K) (pad : K) {X : ℕ} (h : X < nb * 2 ^ l) :
    twoFam nb l l' f f' pad X = f (X / 2 ^ l) (X % 2 ^ l) := if_pos h

/-- The second family of twoFam. -/
theorem twoFam_snd (nb l l' : ℕ) (f f' : ℕ → ℕ → K) (pad : K) {X : ℕ} (h : ¬X < nb * 2 ^ l)
    (h' : X - nb * 2 ^ l < nb * 2 ^ l') :
    twoFam nb l l' f f' pad X =
      f' ((X - nb * 2 ^ l) / 2 ^ l') ((X - nb * 2 ^ l) % 2 ^ l') := by
  unfold twoFam
  rw [if_neg h, if_pos h']

/-- The library's key vector of call 2, written out. -/
theorem keyVec_two [scl : Inst.Model.Scl] (D : Dim) (tb : Inst.Model.Tables) (t : Raw → K)
    (X : ℕ) :
    keyVec D tb t 2 X = twoFam D.nb D.lW D.lX
      (fun b y =>
        key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG) (y / D.ch % D.T) (y % D.ch))
      (fun b y => key3X D t b (y / D.T) (y % D.T)) (((lut D tb 2).pad : ℤ) : K) X := rfl

/-- The library's key vector of call 3, written out. -/
theorem keyVec_three [scl : Inst.Model.Scl] (D : Dim) (tb : Inst.Model.Tables) (t : Raw → K)
    (X : ℕ) :
    keyVec D tb t 3 X = twoFam D.nb D.l4 0
      (fun b y => key4 t b (y / D.ch / D.T) (y / D.ch % D.T) (y % D.ch))
      (fun _ _ => (((lut D tb 3).pad : ℤ) : K)) (((lut D tb 3).pad : ℤ) : K) X := rfl

/-- **The key vectors kvA, written for this library over the verifier's records, are keyVec at every
index in a piece.** -/
theorem kvA_eq_keyVecC (N : NumsA S) {cs : Fin 4 → ACall} (L : LaidA S cs)
    (fs : Model.Forest.Shape) (cell : NameA → K) (c : Fin 4) (X : ℕ)
    (hX : X < (dimOf S).used c) :
    kvA S fs cell c.val X = keyVec (scl := sclOf S) (dimOf S) (tbOf S) (tC S cell) c X := by
  have two : ∀ (q : Fin 4) (s s' : Seg) (l l' : ℕ),
      (∀ b < (dimOf S).nb, pcAt S s l 0 b ∈ (cs q).pcs.toList) →
      (∀ b < (dimOf S).nb, pcAt S s' l' ((dimOf S).nb * 2 ^ l) b ∈ (cs q).pcs.toList) →
      X < (dimOf S).nb * 2 ^ l + (dimOf S).nb * 2 ^ l' →
      (X < (dimOf S).nb * 2 ^ l ∧ kvA S fs cell q.val X =
          segKey S cell (cs q).sh s (X / 2 ^ l / S.HA) (X / 2 ^ l % S.HA) (X % 2 ^ l)) ∨
      (¬X < (dimOf S).nb * 2 ^ l ∧ X - (dimOf S).nb * 2 ^ l < (dimOf S).nb * 2 ^ l' ∧
        kvA S fs cell q.val X =
          segKey S cell (cs q).sh s' ((X - (dimOf S).nb * 2 ^ l) / 2 ^ l' / S.HA)
            ((X - (dimOf S).nb * 2 ^ l) / 2 ^ l' % S.HA)
            ((X - (dimOf S).nb * 2 ^ l) % 2 ^ l')) := by
    intro q s s' l l' h1 h2 hlt
    by_cases h : X < (dimOf S).nb * 2 ^ l
    · refine Or.inl ⟨h, ?_⟩
      have e := kv_fam fs cell q.val (cs q) (L.isCall q) (L.ap q) s l 0 _ h1 X h
      rw [Nat.zero_add] at e
      exact e
    · have h' : X - (dimOf S).nb * 2 ^ l < (dimOf S).nb * 2 ^ l' := by omega
      refine Or.inr ⟨h, h', ?_⟩
      have e := kv_fam fs cell q.val (cs q) (L.isCall q) (L.ap q) s' l'
        ((dimOf S).nb * 2 ^ l) _ h2 (X - (dimOf S).nb * 2 ^ l) h'
      rw [show (dimOf S).nb * 2 ^ l + (X - (dimOf S).nb * 2 ^ l) = X by omega] at e
      exact e
  match c, hX with
  | 0, hX =>
    rcases two 0 .rm .rd _ _ L.rm L.rd hX with ⟨h, e⟩ | ⟨h, h', e⟩
    · rw [e, segKey_rm]
      exact (twoFam_fst _ _ _ _ _ _ h).symm
    · rw [e, segKey_rd]
      exact (twoFam_snd _ _ _ _ _ _ h h').symm
  | 1, hX =>
    rcases two 1 .fm .fd _ _ L.fm L.fd hX with ⟨h, e⟩ | ⟨h, h', e⟩
    · rw [e, L.sh, segKey_fm S cell N]
      exact (twoFam_fst _ _ _ _ _ _ h).symm
    · rw [e, L.sh, segKey_fd S cell N]
      exact (twoFam_snd _ _ _ _ _ _ h h').symm
  | 2, hX =>
    rcases two 2 .wl .ix _ _ L.wl L.ix hX with ⟨h, e⟩ | ⟨h, h', e⟩
    · rw [e, segKey_wl S cell N, keyVec_two (scl := sclOf S), twoFam_fst _ _ _ _ _ _ h]
    · rw [e, segKey_ix S cell N, keyVec_two (scl := sclOf S), twoFam_snd _ _ _ _ _ _ h h']
  | 3, hX =>
    have e := kv_fam fs cell 3 (cs 3) (L.isCall 3) (L.ap 3) .wh (dimOf S).l4 0 _
      L.wh X hX
    rw [Nat.zero_add] at e
    show kvA S fs cell 3 X = _
    rw [e, segKey_wh S cell N, keyVec_three (scl := sclOf S), twoFam_fst _ _ _ _ _ _ hX]

/-- **The same at a list of integer matrices.** -/
theorem kvA_eq_keyVec (N : NumsA S) {cs : Fin 4 → ACall} (L : LaidA S cs)
    (fs : Model.Forest.Shape) (Z : Zs) (c : Fin 4) (X : ℕ) (hX : X < (dimOf S).used c) :
    kvA S fs (cellZ Z : NameA → K) c.val X =
      keyVec (scl := sclOf S) (dimOf S) (tbOf S) (castT (cellsA S Z) : Raw → K) c X :=
  kvA_eq_keyVecC N L fs (cellZ Z) c X hX

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.kv_fam
#print axioms OnBytes.Road.L5.kvA_eq_keyVecC
#print axioms OnBytes.Road.L5.kvA_eq_keyVec
