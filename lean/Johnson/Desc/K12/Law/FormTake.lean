-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FormTake.lean: the length of a sample's seed, as the program has it. Statements
and proofs.

The library's `form_portZ_F` (Johnson/Pack/FormPortZF.lean) and `form_portZ`, `says_sample` and
`says_sample_t` of this folder take "seed.z.length = bitsZ cs s": the message's own cube. The
program's rule is another (OnBytes/Iop/Send.lean, its head: "a seed's point has as many coordinates
as the largest cube, and each message uses the first coordinates, as many as its own cube has"). So
at a message whose cube is smaller than another's of the same prover's message the equality fails.
The premise alone was too tight: `Send.form` takes the prefix itself.
Main names:
  `cube_le`: a cube's main and mask bits are at most its bits; with both tables it has a bit.
  `front_take`: the factor in front (`Send.front`) reads the point's first c.bits coordinates alone:
    its "top" is coordinate number c.bits − 1: the last of the prefix.
  `form_take`: Send.form K s o ⟨z.take (cube K s).bits, β⟩ a = Send.form K s o ⟨z, β⟩ a.
  `readP_take`: readP n reads the first n entries.
  `says_sample_ge`: `says_sample_t` at bitsZ S.codes x.shape ≤ seed.z.length, the point readP (bitsZ
    …) seed.z: by the equality's form at the cut seed.
  `answers_of_says_g`: hS in the form that the join wants: the record's row { row with target := t
    }; "at most"; the codes and the shape as letters cs and sh with S.codes = cs and x.shape = sh.
Limits: still owed for hS at a real member: that the record's x.sampleRows[0] is { row with target
:= t } for row := Send.form … at some seed with β ≠ 0 (Johnson/Desc/K12/Law/SampleOk.lean tests it
at a record, reading a seed back off the row); `runRows` at the statement in front against the
statement behind. No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `cube_bits`
(Johnson/Pack/PortTie.lean); `says_sample_t`, `words_share`, `blank_of_near`, `padded_wordsOf`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.SampleAt

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays

theorem cube_le (K : OnBytes.Codes) (s : OnBytes.OracleShape) :
    (Send.cube K s).mainBits ≤ (Send.cube K s).bits ∧ (Send.cube K s).maskBits ≤ (Send.cube K
        s).bits ∧
      (((Send.cube K s).hasMain && (Send.cube K s).hasMask) = true → 0 < (Send.cube K s).bits) := by
  have hb : (Send.cube K s).bits = if (Send.cube K s).hasMain && (Send.cube K s).hasMask
      then max (Send.cube K s).mainBits (Send.cube K s).maskBits + 1
      else (Send.cube K s).mainBits + (Send.cube K s).maskBits := rfl
  rw [hb]
  split
  · exact ⟨by omega, by omega, fun _ => by omega⟩
  · rename_i h
    exact ⟨by omega, by omega, fun q => absurd q h⟩

/-- The factor in front reads the point's first c.bits coordinates alone. -/
theorem front_take (z : List E) (c : SampleCube) (tb : ℕ) (mask : Bool)
    (hb : (c.hasMain && c.hasMask) = true → 0 < c.bits) :
    Send.front (z.take c.bits) c tb mask = Send.front z c tb mask := by
  unfold Send.front
  by_cases h : (c.hasMain && c.hasMask) = true
  · have h0 := hb h
    have e1 : (z.take c.bits).getD (c.bits - 1) zeroE = z.getD (c.bits - 1) zeroE := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
        if_pos (by omega)]
    have e2 : (z.take c.bits).take (c.bits - 1) = z.take (c.bits - 1) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    simp only [e1, e2]
  · simp only [h, Bool.not_false, if_pos]

/-- Send.form reads the point's prefix alone: at the seed cut to the message's own cube it makes
the same row. -/
theorem form_take (K : OnBytes.Codes) (s : OnBytes.OracleShape) (o : ℕ) (z : List E) (β : E) (a :
    ℕ) :
    Send.form K s o ⟨z.take (Send.cube K s).bits, β⟩ a = Send.form K s o ⟨z, β⟩ a := by
  obtain ⟨hm, hk, hb⟩ := cube_le K s
  unfold Send.form
  simp only [List.take_take, Nat.min_eq_left hm, Nat.min_eq_left hk, front_take _ _ _ _ hb]

theorem readP_take (n : ℕ) (z : List E) : readP n (z.take n) = readP n z := by
  funext i
  show readE ((z.take n).getD i.val zeroE) = readE (z.getD i.val zeroE)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos i.isLt]

/-- says_sample_t under the rule as the program has it: the seed's point has at least as many
coordinates as the message's own cube has bits (all messages of one prover's message share a point
as long as the largest cube; each uses the first coordinates). -/
theorem says_sample_ge (S : Statement) (o : ℕ) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (seed : SampleSeed) (row : Row) (h : Send.form S.codes x.shape o seed 0 = some row) (t : E)
    (h1 : x.shape.answers = 1) (hc : CaseE x.shape ∨ CaseF x.shape)
    (hz : bitsZ S.codes x.shape ≤ seed.z.length) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain S.codes x.shape).ell = (pMain S.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask S.codes x.shape).ell = (pMask S.codes x.shape).ell)
    (m : Words GE) (hP : Padded S m) :
    Says rdE S { row with target := t } m ↔
      (portZ S.codes x.shape).val (readP (bitsZ S.codes x.shape) seed.z, β)
        (fun j => m o (partZ S.codes x.shape j) (locZ S.codes x.shape j)) = fun _ => readE t := by
  have h' : Send.form S.codes x.shape o ⟨seed.z.take (bitsZ S.codes x.shape), seed.beta⟩ 0 =
      some row := by
    rw [← cube_bits, form_take]
    exact h
  have := says_sample_t S o x hx ⟨seed.z.take (bitsZ S.codes x.shape), seed.beta⟩ row h' t h1 hc
    (by show (seed.z.take _).length = _; rw [List.length_take, Nat.min_eq_left hz]) β hβ hlM hlZ m
        hP
  rw [this]
  show (portZ S.codes x.shape).val (readP _ (seed.z.take _), β) _ = _ ↔ _
  rw [readP_take]

/-- hS, in the form that the join wants: at the row that the record holds ({ row with target :=
t }); the point at least as long as the cube; and the codes and the shape as letters cs | sh, tied
to the statement's by two equations: so that the seat may be typed over another statement's codes
(the plain data's) than the one at which the rows are read. -/
theorem answers_of_says_g {s : Sg} (hs : s.Sized) (e : ℕ) (he : e < s.d) (S : Statement) (G' :
    Group)
    (L : GroupLayout) (F : LayFacts S G' L) (y : s.cIn.Word) (hy : RowsBlank s S L y) (o n : ℕ)
    (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x) (cs : OnBytes.Codes) (hcs : S.codes = cs)
    (sh : OnBytes.OracleShape) (hsh : x.shape = sh) (e0 : ℕ) (σs : Site s (mbOfShape cs sh e0))
    (oM oZ : ℕ) (hpM : ∀ r, σs.pM r = vtx _ (oM + r.val)) (hpZ : ∀ r, σs.pZ r = vtx _ (oZ + r.val))
    (hrM : oM + sh.mainRows ≤ 2 ^ (s.h + s.g)) (hrZ : oZ + sh.maskRows ≤ 2 ^ s.h)
    (hf : L.find o = some n) (hk : L.kept.getD n false = false)
    (hm : 0 < sh.mainRows → L.mainFirst.getD n none = some oM)
    (hz : 0 < sh.maskRows → L.maskFirst.getD n none = some oZ)
    (hLk : L.k = s.h + s.g) (hLh : L.h = s.h)
    (seed : SampleSeed) (row : Row) (h : Send.form cs sh o seed 0 = some row) (t : E)
    (h1 : sh.answers = 1) (hc : CaseE sh ∨ CaseF sh)
    (hzl : bitsZ cs sh ≤ seed.z.length) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (hlM : 0 < sh.mainRows → 2 ^ ceilLog2 (pMain cs sh).ell = (pMain cs sh).ell)
    (hlZ : 0 < sh.maskRows → 2 ^ ceilLog2 (pMask cs sh).ell = (pMask cs sh).ell)
    (w : s.cIn.N.Wit) (hn : offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e)
    (hS : Says rdE S { row with target := t } (H2K.ClaimSays.wordsOf S L (tabOf s w.1))) :
    (portOmZ cs sh e0).Z.val (readP (bitsZ cs sh) seed.z, β) (fun j => w.1 (σs.atJ j)) =
      fun _ => readE t := by
  subst hcs
  subst hsh
  have hP := padded_wordsOf F _ (blank_of_near s hs e he S L y hy w hn)
  have h2 := (says_sample_ge S o x hx seed row h t h1 hc hzl β hβ hlM hlZ _ hP).1 hS
  have h3 : (fun j => H2K.ClaimSays.wordsOf S L (tabOf s w.1) o (partZ S.codes x.shape j)
      (locZ S.codes x.shape j)) = fun j => w.1 (σs.atJ j) :=
    funext fun j => words_share S.codes x.shape e0 σs oM oZ hpM hpZ hrM hrZ S L o n x hx rfl hf hk
        hm hz
      hLk hLh w.1 j
  rw [h3] at h2
  exact h2

end H2K.Pin

#print axioms H2K.Pin.form_take
#print axioms H2K.Pin.says_sample_ge
#print axioms H2K.Pin.answers_of_says_g
