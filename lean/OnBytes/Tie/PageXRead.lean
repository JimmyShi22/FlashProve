-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PageXRead.lean: what the typing makes of a chain that the strict reader has read is an
argument string on which the compiled verifier's run at `Tie.famXPd` is its run at the family that
the encoding of OnBytes/Tie/PageXFit.lean reads out of a function on bit strings.

OnBytes/Tie/PageXAsked.lean has that equation for every argument string with `TypedOK`. This file
shows `TypedOK` in two steps. (1) `OutOK`: three facts on what was read: the run's value has 32
bytes; every nonce is below 2^64; the number of words that the typing asks of a stored table's
opened columns is below 2^24. With them, whatever `Run.PQ.toBPrfX` makes of what was read has
`TypedOK`. (2) The strict reader with stored tables, at the hash that any function on byte strings
with answers of 32 bytes induces, hands out only chains with `OutOK`, for a description whose rounds
open trees of the chain's own alone and which has random bytes.

TWO DESCRIPTIONS. The typing and the verifier stand at a description D (`Run.PQ.XD`); the reader
reads under a description S (`Fmt.SpecX`). Asked of the two: they name the same stored tables
(`D.stored = S.stored`). Nothing else ties them here; in particular S's statement is free. So one
D, and with it one encoding, serves readings under all statements.

Main definitions: `OutOK`.
Main theorems.
 `typedOK_of`    `OutOK`, a depth of at most 62, a configuration digest of 32 bytes, a statement of
                fewer than 2^64 bytes, and `toBPrfX .. o = some π` imply `TypedOK`.
 `outOK_read`    what the strict reader hands out has `OutOK`.
 `depth_le`      in a description in order the stored tables' depth is at most 48.
 `read_verifyBSPd`   THE WHOLE: for every pd, every g : Fam (rom 256) and every function O' on byte
                strings with answers of 32 bytes: if the strict reader at `Fmt.HO O'` has read o
                under S, and the typing at D makes π of o, the run of `Compile.Batch.verifyOneProtocol` on π
                at
                `famXPd D dec (digToBytes pd) (oB (g ())) (D.K + 1)` is its run at
                `readBlocks (theImplX (pageXPd ..)) g`.
 `read_verifyBS`   the case of the format's own digest of the parameter bytes.

What is not claimed. Nothing on soundness, and no probability. Nothing on BLAKE2b, but that in
`read_verifyBS` its digest of the parameter bytes stands as a constant in the first query's string.
In both theorems the function O' at which the reader reads and the function g at which the verifier
runs are not tied to each other, nor is pd to either: the theorem is an equation between two runs of
the verifier, and says of neither that it accepts. That the reader reads any file is not said. The
hypotheses `FitsS D.base D.K` (bounds on the description; Run/OneIsTypedTop.lean: `fitsS_of`),
`StmInv D` and the bound on the statement's length are shown at no description here. The program
(the Lean port built from OnBytes/, not the C++ verifier) does not call any function of this file.

-/
import OnBytes.Tie.PageXAsked
import OnBytes.Tie.StoredMain

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-! ## From three facts on what was read to the argument string -/

/-- **Three facts on a chain as read**, for the openings xs of stored tables: the run's value has 32
bytes; the nonces are below 2^64; the columns of the stored tables' openings are to have fewer than
2^24 words. -/
structure OutOK (xs : List XO) (o : Fmt.ChainOut) : Prop where
  /-- the run's value has 32 bytes -/
  run   : ∀ r, o.run = some r → r.size = 32
  /-- every round's nonce fits its word -/
  nonce : ∀ ro ∈ o.rounds.toList, ro.nonce < 2 ^ 64
  /-- the number of words that the typing asks of a stored table's columns -/
  width : ∀ e ∈ storedB xs o, e.2.1 < 2 ^ 24

/-- The first 256 bits of the typed salt of a leaf are the bytes in front, if these are 32. -/
theorem front_leafSalt (cfg s : ByteArray) (hc : cfg.size = 32) :
    bitsToBytes ((leafSalt cfg s).take 256) = cfg := by
  unfold leafSalt
  rw [List.take_left' (by rw [length_bytesToBits, hc]), bitsToBytes_bytesToBits]

variable (D : XD) (dec : View → Bool)

/-- **What the typing makes of a chain with `OutOK` has `TypedOK`**, if the configuration's digest
has 32 bytes, the stored tables' depth is at most 62, and the statement of the two roots has fewer
than 2^64 bytes. -/
theorem typedOK_of (hcfg : D.base.cfg.size = 32) (ha : D.a ≤ 62) (cm cm' : Dig 256)
    (hstm : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64) (o : Fmt.ChainOut)
    (H : OutOK D.xs o) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (hπ : toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π) :
    TypedOK D dec cm cm' π := by
  unfold toBPrfX at hπ
  by_cases hall : (storedB D.xs o).all
      (fun x => x.2.2.ok D.base.plan.salt x.2.1 && x.2.2.a == D.a) = true
  · rw [if_pos hall] at hπ
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hπ
    unfold toBPrfP at hz
    split at hz
    · rename_i run pl e1 e2
      split at hz
      · obtain rfl := Option.some.inj hz
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1
          (show (plainsSL D.C D.ds (offStored D.xs o).rounds.toList).map (fun r => ((), r)) =
            some pl from e2)
        refine ⟨?_, ?_, ?_, hstm⟩
        · show (bytesToBits run).length = 256
          rw [length_bytesToBits, H.run run e1]
        · refine nonces_of D.C D.ds _ r hr fun ro hro => ?_
          have hro' : ro ∈ o.rounds.toList.zipIdx.map fun r =>
              { r.1 with opens := r.1.opens.drop (xsAt D.xs r.2).length } := by
            simpa [offStored] using hro
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hro'
          exact H.nonce y.1 (List.fst_mem_of_mem_zipIdx hy)
        · intro p op hop
          obtain ⟨e, he, -, c, s, pt, hm, rfl⟩ :=
            extOf_found D.a D.base.cfg (storedB D.xs o) p op hop
          refine ⟨front_leafSalt _ _ hcfg, ?_, ?_⟩
          · have hk := List.all_eq_true.1 hall e he
            rw [Bool.and_eq_true] at hk
            have hk1 := hk.1
            unfold OpenB.ok at hk1
            simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk1
            have hc : c ∈ e.2.2.cols := (List.of_mem_zip (List.of_mem_zip hm).2).1
            show c.length < 2 ^ 24
            rw [hk1.1.1.1.2 c hc]
            exact H.width e he
          · show 2 ^ D.a + p.elim (·.val) (·.val) < 2 ^ 64
            have h1 : p.elim (·.val) (·.val) < 2 ^ D.a := by
              rcases p with p | p <;> exact p.isLt
            have h2 : (2 : ℕ) ^ D.a ≤ 2 ^ 62 := Nat.pow_le_pow_right (by omega) ha
            omega
      · cases hz
    · cases hz
  · rw [if_neg hall] at hπ
    cases hπ

/-! ## What the strict reader hands out -/

/-- In a description in order a stored table's column has fewer than 2^24 words, and its tree a
depth of at most 48. -/
theorem specX_small (S : Fmt.SpecX) (hS : S.ok = true) :
    ∀ t ∈ S.stored.flatten, t.sh.W < 2 ^ 24 ∧ t.sh.a ≤ 48 := by
  intro t ht
  obtain ⟨ts, hts, htt⟩ := List.mem_flatten.1 ht
  obtain ⟨r, hr⟩ := exists_zip_left S.base.rounds S.stored ts hts (le_of_eq (specX_len S hS))
  have h := specX_round S hS (r, ts) hr
  unfold Fmt.storedOk at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have hE : ts = [] := List.isEmpty_iff.1 h
    rw [hE] at htt
    cases htt
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
      Fmt.depthOK] at h
    have := h.2 t htt
    exact ⟨this.1.1.1.1.2, this.1.1.1.1.1.1.2⟩

/-- **The stored tables' depth is at most 48**, for a description D that names the stored tables of
a description S in order. -/
theorem depth_le (S : Fmt.SpecX) (hS : S.ok = true) (hsto : D.stored = S.stored) : D.a ≤ 48 := by
  unfold XD.a
  rw [hsto]
  cases hh : S.stored.flatten.head? with
  | none => exact Nat.zero_le _
  | some t => exact (specX_small S hS t (List.mem_of_head? hh)).2

/-- **What the strict reader with stored tables hands out has `OutOK`.** The reader stands at the
hash that a function O' on byte strings with answers of 32 bytes induces; the chain may begin at any
byte, under any record of vertices. Asked of the description S: every tree that a round opens is one
of the chain's own, and the chain has random bytes. -/
theorem outOK_read (O' : ByteArray → ByteArray) (hO : ∀ s, (O' s).size = 32) (S : Fmt.SpecX)
    (hopen : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    (hn : S.base.rand.isNone = false)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O') S seen b i = some (o, j)) :
    OutOK (xsOf S.stored) o := by
  obtain ⟨hSok, x, i0, hd, s, hr, hst', hf, rfl, rfl⟩ := readX_stages (Fmt.HO O') S seen b i o j e
  obtain ⟨rnd, rfl⟩ := rnd_some S.base b i x i0 hn hr
  obtain ⟨hdrun, rho0⟩ := hd
  obtain ⟨-, hrun, -⟩ := startChain_some (Fmt.HO O') _ _ _ _ _ hst'
  obtain ⟨R, hR⟩ : ∃ R : ByteArray, hdrun = some R := ⟨_, hrun⟩
  subst hR
  have hown : ∀ r ∈ S.base.rounds.zip S.stored, ∀ x ∈ r.1.opens, ∃ n, x.2 = .own n :=
    fun r hr' => hopen r.1 (List.of_mem_zip hr').1
  obtain ⟨rc, g1, g2, -, -, g5⟩ := foldX_facts (Fmt.HO O') S.base.cfg S.base.statement S.base.plan
    R b (S.base.rounds.zip S.stored) _ s hown hf
  have hlen := specX_len S hSok
  have hsnd : (S.base.rounds.zip S.stored).map (·.2) = S.stored :=
    List.map_snd_zip (le_of_eq hlen)
  have g1' : s.out.toList = rc.map roundWithStoredOpenings := by simpa using g1
  have hF : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (Fmt.HO O') S.base.cfg S.base.statement p.1.drawn.poss) ts p.2)
      S.stored rc := by
    rw [← hsnd]
    exact List.forall₂_map_left_iff.2 (g5.imp fun _ _ hh => hh.2)
  have hl : List.Forall₂ (fun (ts : List Fmt.Stored)
      (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) => ts.length = p.2.length)
      S.stored rc := hF.imp fun _ _ hh => hh.length_eq
  refine ⟨?_, ?_, ?_⟩
  · intro r hr'
    have e1 : some r = some (Fmt.HO O' 172 0 S.base.label Fmt.zero32 _) := hr'.symm.trans hrun
    rw [Option.some.inj e1]
    exact size_HO O' hO 172 _ _ _ _
  · intro ro hro
    have hro' : ro ∈ rc.map roundWithStoredOpenings := g1' ▸ hro
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hro'
    exact trace_nonce (Fmt.HO O') S.base.plan _ _ _ _ g2 (stripR p.1)
      (List.mem_map.2 ⟨p, hp, rfl⟩)
  · intro y hy
    rw [storedB_eq S.stored _ rc g1' hl] at hy
    obtain ⟨tp, htp, hy'⟩ := List.mem_flatMap.1 hy
    obtain ⟨tz, htz, rfl⟩ := List.mem_map.1 hy'
    have h1 := (List.forall₂_iff_zip.1 hF).2 (show (tp.1, tp.2) ∈ _ from htp)
    have h2 := (List.forall₂_iff_zip.1 h1).2 (show (tz.1, tz.2) ∈ _ from htz)
    show tz.2.1.W < 2 ^ 24
    rw [h2.sh]
    exact (specX_small S hSok tz.1 (List.mem_flatten.2 ⟨tp.1, (List.of_mem_zip htp).1,
      (List.of_mem_zip htz).1⟩)).1

/-! ## The whole -/

/-- **What the typing at D makes of a chain that the strict reader has read under S has `TypedOK`.**
D and S name the same stored tables; nothing else ties them. -/
theorem typedOK_read (hcfg : D.base.cfg.size = 32) (S : Fmt.SpecX) (hsto : D.stored = S.stored)
    (O' : ByteArray → ByteArray) (hO : ∀ s, (O' s).size = 32)
    (hopen : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    (hn : S.base.rand.isNone = false)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O') S seen b i = some (o, j)) (cm cm' : Dig 256)
    (hstm : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (hπ : toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π) :
    TypedOK D dec cm cm' π := by
  have hS : S.ok = true := (readX_stages (Fmt.HO O') S seen b i o j e).1
  have H : OutOK D.xs o := by
    rw [xs_eq, hsto]
    exact outOK_read O' hO S hopen hn seen b i o j e
  exact typedOK_of D dec hcfg (by have := depth_le D S hS hsto; omega) cm cm' hstm o H π hπ

/-- **ON WHAT THE TYPING MAKES OF A CHAIN THAT WAS READ, THE COMPILED VERIFIER'S RUN AT famXPd IS
ITS RUN AT WHAT THE ENCODING READS OUT OF g.** For every pd of 256 bits and every g on bit strings;
pd is tied to neither g nor O'. The reader stands at the hash of any function O' on byte strings
with answers of 32 bytes, under a description S that names the stored tables of D. The other
hypotheses: the configuration's digest has 32 bytes; a reader for the statement (`StmInv D`); the
bounds `FitsS D.base D.K`; every tree that a round of S opens is one of the chain's own; the chain
has random bytes; the statement of the two roots has fewer than 2^64 bytes. An equation between two
runs: of neither is it said that it accepts. Nothing on soundness; no probability. -/
theorem read_verifyBSPd (pd : Dig 256) (hcfg : D.base.cfg.size = 32) (V : StmInv D)
    (F : FitsS D.base D.K)
    (g : Fam (rom 256)) (S : Fmt.SpecX) (hsto : D.stored = S.stored)
    (O' : ByteArray → ByteArray) (hO : ∀ s, (O' s).size = 32)
    (hopen : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    (hn : S.base.rand.isNone = false)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O') S seen b i = some (o, j)) (cm cm' : Dig 256)
    (hstm : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (hπ : toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π) :
    (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embX D dec) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π).det
        (famXPd D dec (digToBytes pd) (oB (g ())) (D.K + 1)) =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embX D dec) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π).det
        (readBlocks (theImplX (pageXPd dec pd (D.K + 1) hcfg V)) g) :=
  verifyBS_readX D dec pd hcfg V F g cm cm' π
    (typedOK_read D dec hcfg S hsto O' hO hopen hn seen b i o j e cm cm' hstm π hπ)

/-- `read_verifyBSPd` at the format's own digest of the parameter bytes: there `Tie.famXPd` is the
library's `Run.PQ.famX`, and the data are `pageX`. -/
theorem read_verifyBS (hcfg : D.base.cfg.size = 32) (V : StmInv D) (F : FitsS D.base D.K)
    (g : Fam (rom 256)) (S : Fmt.SpecX) (hsto : D.stored = S.stored)
    (O' : ByteArray → ByteArray) (hO : ∀ s, (O' s).size = 32)
    (hopen : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    (hn : S.base.rand.isNone = false)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O') S seen b i = some (o, j)) (cm cm' : Dig 256)
    (hstm : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up)
    (hπ : toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π) :
    (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embX D dec) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π).det
        (famX D dec (oB (g ())) (D.K + 1)) =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embX D dec) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π).det
        (readBlocks (theImplX (pageX dec (D.K + 1) hcfg V)) g) := by
  have h := read_verifyBSPd D dec
      (pdX D) hcfg V F g S hsto O' hO hopen hn seen b i o j e cm cm' hstm
    π hπ
  rw [bytes_pdX, ← famX_eq_pd] at h
  exact h

end OnBytes.Tie
