-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SeedIsBehind.lean: code switching (the kind K2): THE SENDINGS' INVARIANT
K1.SeedIs (Johnson/Desc/K1/Law/SeedIs.lean) BEHIND AN ACCEPT OF THE KIND's DECISION, at every new
message with one answer: the verifier's state behind holds the message, with the notice's shape,
marked as sampled, with JUST ONE sample row: the sending kind's own row (K1.sampleRow) at the seed
that round 1 drew. For K12's law at the border behind the last switch, which spends it at the
members of the group under test. NO BLOCK IMPORTS THIS FILE.
  one_row          an array of size 1 whose entry 0 is r is #[r]
  seedIs_behind    at an accept (K2Hears/Whole.lean's AtYes, with the decision's own equation):
                   there are the joint number of bits, the number of answers and the seeds that
                   Send.seedsOf cuts off round 1's drawn elements, and for every new message i
                   with ONE answer, where the three tests on the codes and the shape hold: the
                   factor b is the element behind the joint point, it is not the zero element, the
                   shape's bits are at most the joint ones, and FOR EVERY UNIT β THAT b READS AS:
                   K1.SeedIs codes shape s'.st (number) (the first bits of round 1's drawn
                   elements, read; β) (the answer, read)
PREMISES BESIDE THE ACCEPT, AS IN K1's form_eq (Johnson/Desc/K1/Law/FormEq.lean): hl: every code's
message length is a power of two (codes.lengthsOk) · hs: Blk.shapeOk codes shape · hp: the shape's
pads fit: THREE TESTS WITH CODE ON THE LIST OF ROUNDS. AND: b reads as a unit's value (the text
tests isZeroE alone: an element that is not in order can read as 0). BY: K2.sent_rows
(K2Hears/SentRows.lean) · seedsOf_head | seedsOf_len (K2Hears/SeedBehind.lean) · K1.form_eq ·
K2.yes_mark (Tw/K2C/HeldAtYes.lean) · AtYes' sent | same | tables.
LIMITS. One answer a message. It travels on by K1.SeedIs.travels | Sound.seedIs_of_part: not
called here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.SeedBehind
import Johnson.Top.H0.Tw.K2C.HeldAtYes
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Desc.K1.Law.FormEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model OnBytes.Slice Johnson.Pack
open _root_.Tw.K2 (switchNotices sendByL8)

theorem one_row {α : Type} {a : Array α} {r : α} (hz : a.size = 1) (h0 : a[0]? = some r) :
    a = #[r] := by
  apply Array.ext
  · simpa using hz
  · intro i h1 h2
    have hi : i = 0 := by omega
    subst hi
    have e := Array.getElem?_eq_getElem h1
    rw [h0] at e
    simpa using (Option.some.inj e).symm

theorem seedIs_behind {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (hd : decideWith sendByL8 p s [r₁, r₂] gs = .ok s')
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) :
    ∃ (bits answers : Nat) (seeds : List SampleSeed),
      Send.seedsOf bits answers (r₁.drawn.elems.map E.ofTriple) = some seeds ∧
      ∀ (i : Nat) (n : OracleNotice), (switchNotices x.T x.others)[i]? = some n →
        n.shape.answers = 1 → x.st.codes.lengthsOk = true →
        Blk.shapeOk x.st.codes n.shape = true →
        (K1.Msg.of x.st.codes n.shape).padFits = true →
        ∃ b t : E, (r₁.drawn.elems.map E.ofTriple)[bits]? = some b ∧ isZeroE b = false ∧
          bitsZ x.st.codes n.shape ≤ bits ∧
          ∀ β : GEˣ, (β : GE) = readE b →
            K1.SeedIs x.st.codes n.shape s'.st (x.st.oracles.size + i)
              (readP (bitsZ x.st.codes n.shape) (r₁.drawn.elems.map E.ofTriple), β)
              (readE t) := by
  obtain ⟨bits, answers, seeds, hseeds, hbeta, hall, -⟩ := sent_rows A.sentBy
  refine ⟨bits, answers, seeds, hseeds, fun i n hn h1 hl hs hp => ?_⟩
  obtain ⟨hle, rws, hrws, hsz, hrow⟩ := hall i n hn (by omega)
  obtain ⟨seed, row, yv, hs0, hform, hr0⟩ := hrow 0 (by omega)
  obtain ⟨hz, hb⟩ := seedsOf_head bits answers _ seeds seed hseeds hs0
  have hlen := seedsOf_len bits answers _ seeds hseeds seed (List.mem_of_getElem? hs0)
  rw [cube_bits] at hle
  refine ⟨seed.beta, yv, hb, hbeta seed (List.mem_of_getElem? hs0), hle, fun β hβ => ?_⟩
  obtain ⟨xo, hxo, hmk⟩ := yes_mark hd A.front i n hn (by omega)
  have hst : (s'.st.oracles[x.st.oracles.size + i]?).map (·.sampleRows) = some rws :=
    (A.tables.samples _).trans ((A.same.samples _).trans hrws)
  have hsh : (s'.st.oracles[x.st.oracles.size + i]?).map (·.shape) = some n.shape := by
    rw [A.tables.shape, A.same.shape, A.sent.shape, hn]
    rfl
  rw [hxo] at hst hsh
  have e1 : xo.sampleRows = rws := Option.some.inj hst
  have e2 : xo.shape = n.shape := Option.some.inj hsh
  have hc : s'.st.codes = x.st.codes :=
    A.tables.codes.trans (A.same.codes.trans A.sent.codes)
  have hfe := K1.form_eq x.st.codes n.shape (x.st.oracles.size + i) seed.z seed.beta 0 yv hl hs hp
  have hform' : Send.form x.st.codes n.shape (x.st.oracles.size + i) ⟨seed.z, seed.beta⟩ 0 =
      some row := hform
  rw [hform'] at hfe
  have hrw : ({ row with target := yv } : OnBytes.Row) =
      K1.sampleRow (K1.Msg.of x.st.codes n.shape) (x.st.oracles.size + i) seed.z
        seed.beta 0 yv := Option.some.inj hfe
  refine ⟨hc, xo, seed.z, seed.beta, yv, hxo, e2, hmk, ?_, ⟨?_, fun t => ?_, hβ.symm⟩, rfl⟩
  · rw [e1, ← hrw]
    exact one_row (by rw [hsz, h1]) hr0
  · rw [hlen]
    exact hle
  · have ht := t.isLt
    show readL seed.z t.val = readL (r₁.drawn.elems.map E.ofTriple) t.val
    unfold readL
    rw [hz]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.seedIs_behind
