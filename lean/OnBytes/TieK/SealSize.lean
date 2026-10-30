-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/SealSize.lean: a seal that the program's strict reader hands out has 32 bytes.

A chain's seal is the digest that its last round drew (`ChainRead.seal`,
OnBytes/Chain/Session.lean). By its spelling every digest that a round draws is four words of eight
bytes each (`Fmt.drawSeal`, Fmt/Rules6.lean). So the length needs nothing of the hash, of the plan's
entry, of the work or of the round's kind.

Main names:
  `size_drawSeal`: the four words as a string have 32 bytes.
  `drawRound_digest_size`: a digest in what a round draws has 32 bytes.
  `roundX_good`, `foldX_good`: every round that the strict reader hands out has that property.
  `seal_size`: where the program's reader returns, a seal of what it has read has 32 bytes.
  `ThreeChains.seal1_size`, `ThreeChains.seal2_size`: the two seals of a file's flat record.
Limits: it claims nothing on soundness. It does not say which block of the hash's answer the seal
is. The program does not import this file.

-/
import OnBytes.Tie.StoredRead
import OnBytes.Tie.StoredDom
import OnBytes.Chain.ReaderLaws
import OnBytes.TieK.Chains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open _root_.Run OnBytes.Tie

/-- The four words of a seal, as a string, have 32 bytes. -/
theorem size_drawSeal (row : Fmt.Row) (c : Nat) : (Fmt.drawSeal row c).1.size = 32 := by
  simp only [Fmt.drawSeal, Fmt.drawWords, Fmt.Dr.times, Fmt.Dr.bind, Fmt.Dr.pure, Fmt.Dr.word,
    List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil, ByteArray.size_append, Fmt.size_u64]
  rfl

/-- A digest in what a round draws has 32 bytes. -/
theorem drawRound_digest_size (f : Fmt.Fld) (e : Fmt.Entry) (k : Fmt.Kind) (row : Fmt.Row)
    (d : ByteArray) (h : (Fmt.drawRound f e k row).digest = some d) : d.size = 32 := by
  simp only [Fmt.drawRound, Fmt.drawRoundD, Fmt.Dr.bind, Fmt.Dr.pure, Fmt.drawDigest] at h
  split at h
  · simp only [Fmt.Dr.bind, Fmt.Dr.pure] at h
    injection h with h'
    rw [← h']
    exact size_drawSeal _ _
  · simp only [Fmt.Dr.pure] at h
    cases h

/-- A round as handed out: a digest that it drew has 32 bytes. -/
def GoodRound (ro : Fmt.RoundOut) : Prop := ∀ d, ro.drawn.digest = some d → d.size = 32

section
variable (h : HId)

/-- A round that is read adds one good round to what is handed out. -/
theorem roundX_good (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s s' : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored)
    (e : Fmt.roundX (m := Id) h cfg statement P run b s r ts = some s')
    (hs : ∀ ro ∈ s.out, GoodRound ro) : ∀ ro ∈ s'.out, GoodRound ro := by
  unfold Fmt.roundX at e
  split at e
  · cases e
  · split at e
    · cases e
    · split at e
      · cases e
      · simp only [idb] at e
        split at e
        · cases e
        · split at e
          · cases e
          · split at e
            · cases e
            · split at e
              · cases e
              · cases e
                intro ro hro
                rcases Array.mem_push.1 hro with hm | rfl
                · exact hs ro hm
                · exact fun d hd => drawRound_digest_size _ _ _ _ d hd

/-- All rounds that are read are good. -/
theorem foldX_good (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s s' : Fmt.St),
      Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s = some s' →
      (∀ ro ∈ s.out, GoodRound ro) → ∀ ro ∈ s'.out, GoodRound ro
  | [], s, s', e, hs => by
    cases e
    exact hs
  | r :: rs, s, s', e, hs => by
    simp only [Fmt.foldRoundsX, idb] at e
    cases hst : Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
    | none =>
      rw [hst] at e
      cases e
    | some s1 =>
      rw [hst] at e
      exact foldX_good cfg statement P run b rs s1 s' e
        (roundX_good h cfg statement P run b s s1 r.1 r.2 hst hs)

/-- Every round of a chain that the strict reader has read is good. -/
theorem readX_good (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) (o : Fmt.ChainOut)
    (j : Nat) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    ∀ ro ∈ o.rounds, GoodRound ro := by
  obtain ⟨-, x, i0, hd, s, -, -, hf, ho, -⟩ := readX_stages h S seen b i o j e
  subst ho
  exact foldX_good h _ _ _ _ _ _ _ _ hf (fun ro hro => by simp at hro)

end

/-- **Where the program's reader returns, a seal of what it has read has 32 bytes.** -/
theorem seal_size (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) (r : ChainRead)
    (sl : ByteArray) (e : readChain S seen b i = some (r.out, r.next))
    (hs : r.seal = some sl) : sl.size = 32 := by
  rw [readChain_eq] at e
  have hg := readX_good Fmt.formatHash S seen b i r.out r.next e
  unfold ChainRead.seal at hs
  cases hb : r.out.rounds.back? with
  | none =>
    rw [hb] at hs
    cases hs
  | some x =>
    rw [hb] at hs
    exact hg x (Array.mem_of_back? hb) sl hs

/-- The first seal of a file's flat record has 32 bytes. -/
theorem ThreeChains.seal1_size {p : Proof.TailPublic} {block1 : Blk Proof.FirstEnd}
    {start1 : Start} {file : ByteArray} {i : Nat} {rounds1 : Params.Rounds} {dry : Proof.FirstEnd}
    {S1 : Fmt.SpecX} {r : Proof.TailRead} {seal1 seal2 : ByteArray} {rounds2 : Params.Rounds}
    {dry2 : Proof.SharedEnd} {S2 : Fmt.SpecX} {rounds3 : Params.Rounds} {S3 : Fmt.SpecX}
    {real : Proof.FirstEnd} {real2 : Proof.SharedEnd}
    (h : ThreeChains p block1 start1 file i rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3
      real real2) : seal1.size = 32 :=
  seal_size _ _ _ _ _ _ h.first_read h.first_seal

/-- The second seal of a file's flat record has 32 bytes. -/
theorem ThreeChains.seal2_size {p : Proof.TailPublic} {block1 : Blk Proof.FirstEnd}
    {start1 : Start} {file : ByteArray} {i : Nat} {rounds1 : Params.Rounds} {dry : Proof.FirstEnd}
    {S1 : Fmt.SpecX} {r : Proof.TailRead} {seal1 seal2 : ByteArray} {rounds2 : Params.Rounds}
    {dry2 : Proof.SharedEnd} {S2 : Fmt.SpecX} {rounds3 : Params.Rounds} {S3 : Fmt.SpecX}
    {real : Proof.FirstEnd} {real2 : Proof.SharedEnd}
    (h : ThreeChains p block1 start1 file i rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3
      real real2) : seal2.size = 32 :=
  seal_size _ _ _ _ _ _ h.shared_read h.shared_seal

end OnBytes.TieK

#print axioms OnBytes.TieK.seal_size
