-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WordsMade.lean: the code switch: THE NEW WORDS BY MAKE, AND `Rides`
(BehindPaid.lean) PAID. The words of the messages that the switch sends are read by the table of
joints' own reading of strings as the library's words (`wordsOf`, Johnson/Desc/Sound/MsgSig.lean):
in the game off the first written message, behind the block off the oracles; the two agree.

Main names:
  `colMsg`, `strsMsg`: the columns that a written round's message brings for its own trees, as plain
    strings under the numbers from base on.
  `col_sent`: behind a stretch of two written rounds a tree that the first sends holds what the
    message brought (beside `colStays`, Johnson/Desc/Sound/StringsStay.lean, which speaks of the
    trees in front).
  `words_sent`: so the typed words of members that sit in such trees.
  `wordsMade`: the letter ρ of the law, made. `strMadeB`: the letter strB, made.
  `rides_made`: `Rides` at the plain letters and these makes, whatever on, strs and inX are, from
    ONE FACT ON THE PLAN: each new member's tree is one that the first written round sends.
Limits. Which tree and tenant holds a member, the description G and base are letters: that they are
the description's is not said. Where a column has not its words `wordsOf` falls to 0 (MsgSig.lean's
own limit). The rider's word is laid 0: nothing is asked of it. Nothing on soundness. On hiding
nothing.

-/
import Johnson.Top.H0.K2Caller.PlainAt
import Johnson.Desc.Sound.MsgSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (Frame Piece below strsOf colAt behind wordsOf wordAt)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

/-- The column at leaf x of a written round's own tree number n, off the prover's message. -/
def colMsg (d : RDT) (m : (wT d).Msg) (n x : ℕ) : Option (List UInt64) :=
  (posAtT d.trees n x).map fun q => colT d.trees q (m.1 q)

/-- The strings that a written round's message brings: its own trees' columns, under the numbers
from base on; at the leaves that the frame has. -/
def strsMsg (F : Frame) (base : ℕ) (d : RDT) (m : (wT d).Msg) : Strs :=
  ⟨fun _ => none, fun j x => ((posL F.all j x).map fun _ => (colMsg d m (j - base) x).getD []).getD
      []⟩

/-- **Behind a stretch, a tree that its first round sends holds what the message brought.** -/
theorem col_sent (F : Frame) (base : ℕ) (d₁ d₂ : RDT) (y : F.E.Str)
    (τ : Tr (uLT (ckP .two) [d₁, d₂])) (j x : ℕ) (hb : base ≤ j)
    (hj : j - base < d₁.trees.length) :
    colAt F (behind (ckP .two) F base [d₁, d₂] y τ) j x = (strsMsg F base d₁ τ.1).col j x := by
  show ((posL F.all j x).map (behind (ckP .two) F base [d₁, d₂] y τ).2).getD [] =
    ((posL F.all j x).map fun _ => (colMsg d₁ τ.1 (j - base) x).getD []).getD []
  cases hp : posL F.all j x with
  | none => rfl
  | some q =>
    show sLeft (ckP .two) (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y τ q =
      (colMsg d₁ τ.1 (j - base) x).getD []
    rw [VerifiableInference.Desc.Sound.sLeft_at (ckP .two) F [d₁, d₂] base y τ j x q hp,
      VerifiableInference.Desc.Sound.sCol_eq,
      if_neg (Nat.not_lt.2 hb), colAtST_cons, if_pos hj]
    rfl

/-- So the typed word of a member whose tree the first round sends. -/
theorem words_sent {Xi : Type} (G : FileDescription Xi) (cs : Codes) (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (F : Frame) (base : ℕ) (d₁ d₂ : RDT) (y : F.E.Str)
    (τ : Tr (uLT (ckP .two) [d₁, d₂]))
    (hs : ∀ i, base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length) :
    wordsOf G cs l seat (strsOf F (behind (ckP .two) F base [d₁, d₂] y τ)) =
      wordsOf G cs l seat (strsMsg F base d₁ τ.1) := by
  funext i
  have e : wordOf G (strsOf F (behind (ckP .two) F base [d₁, d₂] y τ)) (seat i).1 (seat i).2 =
      wordOf G (strsMsg F base d₁ τ.1) (seat i).1 (seat i).2 := by
    funext x
    show (G.oracleAt (seat i).1).bind (fun o => o.cut (seat i).2
      (colAt F (behind (ckP .two) F base [d₁, d₂] y τ) (seat i).1 x)) = _
    rw [col_sent F base d₁ d₂ y τ (seat i).1 x (hs i).1 (hs i).2]
    rfl
  unfold VerifiableInference.Desc.Sound.wordsOf VerifiableInference.Desc.Sound.wordAt
  rw [e]

variable {F : Frame} {W : Type}

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  {Xi : Type} (G : FileDescription Xi) (seat : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT)

/-- **The new words BY MAKE, off the first written message**: the table of joints' own reading of
strings as the library's words (`wordsOf`, Johnson/Desc/Sound/MsgSig.lean) at the strings that the
message brings. The rider's word: 0: nothing is asked of it. -/
noncomputable def wordsMade (F : Frame) : WordsOf (selZ (Letters.plain r H) iJ iQ) d₁ :=
  ⟨fun m => wordsOf G r.cs r.l seat (strsMsg F base d₁ m), fun _ => 0⟩

/-- **All words behind BY MAKE, off the oracles behind**: the same reading. -/
noncomputable def strMadeB (a' : Rec × F.E.Str) : (selLoc (Letters.plain r H) iJ iQ).S.ext.Str :=
  (selZ (Letters.plain r H) iJ iQ).sw.S₀.join (selZ (Letters.plain r H) iJ iQ).sw.d.N
    (T := OMsg.Str) (fun i => isEmptyElim i) (wordsOf G r.cs r.l seat (strsOf F a'.2))

variable (p : K2.P2)
  (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
  (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X)

/-- **`Rides` IS PAID at the plain letters and these makes**, whatever on, strs and inX are: from
    one
fact on the plan: each new member's tree is one that the first written round sends. -/
theorem rides_made (on : Rec × F.E.Str → Prop)
    (hs : ∀ i, base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length) :
    Rides (W := W) (Letters.plain r H) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p base ext
        strs
      inX on (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seat) (fun _ => ((), ())) := by
  refine ⟨fun _ _ _ _ _ => funext fun i => ((plain_empty iJ iQ).false i).elim, fun a a' τ _ ho =>
      ?_,
    fun _ _ _ _ _ => rfl⟩
  have h1 : (if sTests (ckP .two) (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) a.2 τ = true
      then (k2Piece (W := W) (Letters.plain r H) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p
        base ext).run a.1 (sView (ckP .two) (VerifiableInference.Desc.Sound.stg F base [d₁, d₂])
          a.2 τ) else none).map
        (fun xo => (xo, behind (ckP .two) F base [d₁, d₂] a.2 τ)) = some a' := ho
  obtain ⟨s', -, h3⟩ := Option.map_eq_some_iff.1 h1
  subst h3
  have e1 : ∀ x x' : (selZ (Letters.plain r H) iJ iQ).sw.S₀.ext.Str, x = x' :=
    fun _ _ => funext fun i => ((plain_empty iJ iQ).false i).elim
  unfold strMadeB
  rw [e1 (fun i => isEmptyElim i) (lawFa (Letters.plain r H) iJ iQ strs inX a).2.2,
    words_sent G r.cs r.l seat F base d₁ d₂ a.2 τ hs]
  rfl

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.col_sent
#print axioms VerifiableInference.Desc.First.K2Caller.words_sent
#print axioms VerifiableInference.Desc.First.K2Caller.rides_made
