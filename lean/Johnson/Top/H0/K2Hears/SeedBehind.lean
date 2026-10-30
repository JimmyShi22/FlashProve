-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/SeedBehind.lean: the code switch: THE SAMPLE ROWS THAT THE RECORD
BEHIND HOLDS, READ AS LINEAR FORMS ON A NEW MESSAGE, ARE THE LIBRARY's SAMPLE ROWS AT THE SEED THAT
ROUND 1 DREW.

The chain's record keeps a message's sample ROWS, not its seed. Johnson/Desc/Sound/Seed.lean ties
the seed to the record by the rows (SeedIs forms a s i ρ := forms a s i = some (Z.mat ρ), forms a
letter: «the reading of the program's plain rows […] as linear forms on the library's typed message
is the law of the sending's kind»). Here that reading is written and the law is shown for the
sending that K2 runs.
  form_take    the program's Send.form reads of a seed's point the first (cube's bits) coordinates
               alone
  front_take, seedsOf_total  tools: Send.front reads the first (cube's bits) coordinates alone; what
               Send.seedsOf cuts has just n (bits + 1) elements
  formsAt      THE READING: the stored sample row number 0 of the message number o, as a linear form
               on the entries of a message of the shape sh: the row's coefficient at the entry's
               table and index
  ansAt        its target, read in the field
  seed_behind  at a yes of the kind's decision (Whole.lean's AtYes): for every new message with ONE
               answer: formsAt at the record BEHIND is the library's portZ matrix at (the first
               bitsZ of round 1's drawn elements, read; the factor: the element behind the joint
               point, read)
By SentRows.lean's sent_rows; form_portZ_F (Johnson/Pack/FormPortZF.lean) and form_portZ_E, joined
in form_portZ (both in Johnson/Desc/K12/Law/FormPortZE.lean).
PREMISES beside the yes: one answer; the shape is CaseE (it has a mask row, or main rows of degree
3) or CaseF (no mask row and main rows of degree 1): shut out is a shape without a mask row whose
degree is neither 1 nor 3; the factor as drawn reads as a unit's value (the text tests isZeroE
alone: an element that is not in order can read as 0).
Near kin of form_take: form_take in OnBytes/Slice/BlkSendTake.lean, which this file does not import
and which is general in the number of coordinates kept: one of the two should go.
LIMITS. WHICH answer is the target: AnsBehind.lean. The typed joint seed's cut into members' seeds:
K2Hands/SeedJoint.lean. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.Whole
import Johnson.Top.H0.K2Hears.SentRows
import Johnson.Desc.K12.Law.FormPortZE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model OnBytes.Slice Johnson.Pack
open _root_.Tw.K2 (switchNotices sendByL8)

theorem front_take (z : List E) (c : SampleCube) (k : Nat) (m : Bool)
    (hp : (c.hasMain && c.hasMask) = true → 0 < c.bits) :
    Send.front (z.take c.bits) c k m = Send.front z c k m := by
  unfold Send.front
  by_cases h : (c.hasMain && c.hasMask) = true
  · have h0 := hp h
    simp only [h, Bool.not_true, Bool.false_eq_true, if_false]
    have e1 : (z.take c.bits).getD (c.bits - 1) zeroE = z.getD (c.bits - 1) zeroE := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_take_of_lt (by omega)]
    have e2 : (z.take c.bits).take (c.bits - 1) = z.take (c.bits - 1) := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [e1, e2]
  · simp [h]

/-- **Send.form reads the first (cube's bits) coordinates alone.** -/
theorem form_take (codes : Codes) (s : OracleShape) (o : Nat) (z : List E) (β : E) (a : Nat) :
    Send.form codes s o ⟨z.take (Send.cube codes s).bits, β⟩ a = Send.form codes s o ⟨z, β⟩ a := by
  have hb : (Send.cube codes s).mainBits ≤ (Send.cube codes s).bits ∧
      (Send.cube codes s).maskBits ≤ (Send.cube codes s).bits ∧
      (((Send.cube codes s).hasMain && (Send.cube codes s).hasMask) = true →
        0 < (Send.cube codes s).bits) := by
    unfold Send.cube
    dsimp only
    by_cases a1 : 0 < s.mainRows <;> by_cases a2 : 0 < s.maskRows <;> simp only [a1, a2] <;>
      refine ⟨?_, ?_, ?_⟩ <;>
      first
        | (simp; done)
        | (simp; omega)
        | exact Nat.le_succ_of_le (Nat.le_max_left _ _)
        | exact Nat.le_succ_of_le (Nat.le_max_right _ _)
  unfold Send.form
  simp only [front_take z _ _ _ hb.2.2, List.take_take, Nat.min_eq_left hb.1,
    Nat.min_eq_left hb.2.1]

/-- What Send.seedsOf cuts has just n (bits + 1) elements. -/
theorem seedsOf_total (bits : Nat) : ∀ (n : Nat) (l : List E) (seeds : List SampleSeed),
    Send.seedsOf bits n l = some seeds → l.length = n * (bits + 1)
  | 0, [], _, _ => by simp
  | 0, _ :: _, seeds, h => by simp [Send.seedsOf] at h
  | n + 1, l, seeds, h => by
    unfold Send.seedsOf at h
    split at h
    · cases h
    · rename_i beta rest hd
      obtain ⟨t, ht, -⟩ := Option.map_eq_some_iff.1 h
      have e := seedsOf_total bits n rest t ht
      have e2 := congrArg List.length hd
      rw [List.length_drop, List.length_cons, e] at e2
      rw [Nat.succ_mul]
      omega

/-- **The reading**: the stored sample row number 0 of the message o, as a linear form on the
entries of
a message of the shape sh. -/
def formsAt (cs : Codes) (sh : OracleShape) (St : Statement) (o : Nat) :
    Option (Unit → (portCode cs sh).J → GE) :=
  (St.oracles[o]?).bind fun x => (x.sampleRows[0]?).map fun row _ j =>
    coefAt row o (partZ cs sh j) (locZ cs sh j)

/-- Its target. -/
def ansAt (St : Statement) (o : Nat) : Option (Unit → GE) :=
  (St.oracles[o]?).bind fun x => (x.sampleRows[0]?).map fun row _ => readE row.target

/-- **The record behind holds the library's sample rows at the seed that round 1 drew.** -/
theorem seed_behind {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) :
    ∃ (bits answers : Nat) (seeds : List SampleSeed),
      Send.seedsOf bits answers (r₁.drawn.elems.map E.ofTriple) = some seeds ∧
      ∀ (i : Nat) (n : OracleNotice),
      (switchNotices x.T x.others)[i]? = some n → n.shape.answers = 1 →
      (CaseE n.shape ∨ CaseF n.shape) →
      ∃ b : E, (r₁.drawn.elems.map E.ofTriple)[bits]? = some b ∧ isZeroE b = false ∧
        bitsZ x.st.codes n.shape ≤ bits ∧
        ∀ β : GEˣ, (β : GE) = readE b →
          formsAt x.st.codes n.shape s'.st (x.st.oracles.size + i) =
            some ((portZ x.st.codes n.shape).mat
              (readP (bitsZ x.st.codes n.shape) (r₁.drawn.elems.map E.ofTriple), β)) := by
  obtain ⟨bits, answers, seeds, hseeds, hbeta, hall, -⟩ := sent_rows A.sentBy
  refine ⟨bits, answers, seeds, hseeds, fun i n hn h1 hc => ?_⟩
  obtain ⟨hle, rws, hrws, -, hrow⟩ := hall i n hn (by omega)
  obtain ⟨seed, row, yv, hs0, hform, hr0⟩ := hrow 0 (by omega)
  obtain ⟨hz, hb⟩ := seedsOf_head bits answers _ seeds seed hseeds hs0
  have hlen := seedsOf_len bits answers _ seeds hseeds seed (List.mem_of_getElem? hs0)
  rw [cube_bits] at hle
  refine ⟨seed.beta, hb, hbeta seed (List.mem_of_getElem? hs0), hle, fun β hβ => ?_⟩
  have hst : (s'.st.oracles[x.st.oracles.size + i]?).map (·.sampleRows) = some rws :=
    (A.tables.samples _).trans ((A.same.samples _).trans hrws)
  obtain ⟨xo, hxo, hxr⟩ := Option.map_eq_some_iff.1 hst
  have hf2 : Send.form x.st.codes n.shape (x.st.oracles.size + i)
      ⟨seed.z.take (Send.cube x.st.codes n.shape).bits, seed.beta⟩ 0 = some row := by
    rw [form_take]
    exact hform
  have hl2 : (seed.z.take (Send.cube x.st.codes n.shape).bits).length =
      bitsZ x.st.codes n.shape := by
    rw [List.length_take, hlen, cube_bits]
    omega
  have hP : readP (bitsZ x.st.codes n.shape) (seed.z.take (Send.cube x.st.codes n.shape).bits) =
      readP (bitsZ x.st.codes n.shape) (r₁.drawn.elems.map E.ofTriple) := by
    funext t
    have ht := t.isLt
    unfold readP readL
    rw [hz, List.take_take, cube_bits, Nat.min_eq_left hle]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht]
  unfold formsAt
  rw [hxo]
  simp only [Option.bind_some]
  rw [hxr, hr0]
  simp only [Option.map_some]
  congr 1
  funext u j
  rw [← hP]
  exact H2K.Pin.form_portZ x.st.codes n.shape _ _ row hf2 h1 hc hl2 β hβ j

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.form_take
#print axioms VerifiableInference.Desc.First.K2.seed_behind
