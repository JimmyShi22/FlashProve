-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/CutsOfChains.lean: from a file's three chains as the program has read them to the yes
of the compiled verifier of a file with three joined chains: the statement, with one named
hypothesis for each premise of `Cuts`.

`TypedOracleCompiler.Joined.Cuts` (OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean) lists what is asked for a yes of the
compiled verifier of a file, cut by cut; `FileW.yes_of_cuts` concludes the yes. This file states
each of its 26 premises at a typing of what one fixed reading of a file gives.

The typing stands as letters (`Typing`). From the public input it gives the file's rounds and the
file as it is written into the typed queries. From the public input and the reading's data it gives
the outer roots, the instance, the proof string, what the three chains yield, the forests, the slot
value and the trace of hash calls.

Main names:
  `Stmt`: a statement in the letters of `Cuts`.
  `Fld.run₁` ... `Fld.accept`: the premises of `Cuts`, one by one, each as such a statement.
  `Typing Pub Dat`: the typing. Pub: the public input; Dat: the reading's data.
  `Typing.Hole Good S`: at every public input and data that are `Good`, the statement S holds at
    the typing's values.
  `CutHoles T Good`: all premises as named hypotheses.
  `yes_of_holes`: they give the yes of the compiled verifier at every good reading.
  `KeyGood`, `ProofGood` (OnBytes/TieK/Good.lean): the readings of a key file and of a proof file at
    which the program's three chains were read and judged.
  `key_yes`, `proof_yes`: `yes_of_holes` at these, from all that the exit code 0 says.
Limits: every field of `CutHoles` is a hypothesis. No typing is given here, and nothing shows that
one exists at which they hold. By its type the typing makes the file's rounds from the public input
alone: that the program's rounds do not hang on a table's values is thereby asked, not shown.
A proof string has one opening at a position; where a file opens one position at two lists the
program ties the two columns by one leaf digest: at a typing that lays a file's own columns and
decides as the program does, `accept` or a walk could fail at an accepted file with two different
columns under one leaf digest: that no such file is accepted is asked within them there, and named
nowhere. The theorem is worth what its typing is worth: at a decision that
says yes to everything `accept` is met. (The head of OnBytes/TypedOracleCompiler/Joined/K/LeftOfChains.lean says the
like of both.)
The hash is fixed: `KeyGood`, `ProofGood` and `K.PortYesAt` speak of the program's own readers
(`readChain`, OnBytes/Chain/Reader.lean), which take no hash as an argument. None is drawn, and
there is no probability. The yes of the compiled verifier is a yes in the trace of hash calls that
the typing gives (`tr`): a letter, tied to no function.
Nothing on soundness. The program does not import this file.

-/
import OnBytes.TypedOracleCompiler.Joined.YesByCuts
import OnBytes.TieK.HolesOfChains
import OnBytes.TieK.Good

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace OnBytes.TieK
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

/-! ## The premises of `Cuts`, one by one -/

section Fields
variable {I X : Type}

/-- A statement in the letters of `Cuts`. -/
abbrev Stmt (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (G : Chains) (Y : Type) (E : ExtSpec) : Type :=
  (sMT sFS : ℕ) → (t : Tag) → (D : Desc G Y E) → (wq : ProtocolQueryLayout lam K D.batch) →
    (embS : (p : OPos G.sh) → OSym G.sh p → Body L) →
    (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)) → (xin : Y → Option X) →
    (embE : E.Sym → Body L) → (depthReq : ℕ) → (cms : List (Dig lam)) → (x : Y) →
    (π : OneProtocolProof lam D.batch) → (a : Out lam G.c₁) → (b : Out lam G.c₂) → (e : Out lam G.c₃) →
    (tr : Trace (typedOracleFamily lam K L)) → (F₁ F₂ F₃ Fe : List (Forest lam L)) → (c : Dig lam) → Prop

variable {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {G : Chains} {Y : Type} {E : ExtSpec}

/-- chain 1 runs in the trace, from the start -/
@[reducible] def Fld.run₁ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    RunsIn tr (TypedOracleCompiler.Joined.run₁ t D wq embP xin cms x π) (some a)

/-- chain 2 runs on from where chain 1 ended -/
@[reducible] def Fld.run₂ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    RunsIn tr (TypedOracleCompiler.Joined.run₂ t D wq embP xin cms x π a) (some b)

/-- chain 3 runs on from where chain 2 ended -/
@[reducible] def Fld.run₃ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    RunsIn tr (TypedOracleCompiler.Joined.run₃ t D wq embP xin cms x π a b) (some e)

/-- chain 3 ends with the slot value c -/
@[reducible] def Fld.thirdChainEndsAtGivenValue : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    e.2.2.slotVal = some c

/-- the format: chain 1's salt has sFS bits -/
@[reducible] def Fld.salt : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    π.salt.length = sFS

/-- the format, over the whole: no root beyond those that the three chains have taken -/
@[reducible] def Fld.roots : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    π.roots.length ≤ RootsOfChain.count G.c₁ a.2.1 + (RootsOfChain.count G.c₂ b.2.1 + RootsOfChain.count G.c₃ e.2.1)

/-- the format: the slot's number is the number of a slot -/
@[reducible] def Fld.slot : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    π.slot < 2 ^ depthReq

/-- the format of the openings at chain 1's rounds -/
@[reducible] def Fld.strict₁ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    strictSB sMT G.c₁ G.A₁ (wire₁ wq) a.2.1 (rd₁ D wq x π a b e) (op₁ D π) = true

/-- at chain 2's rounds -/
@[reducible] def Fld.strict₂ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    strictSB sMT G.c₂ G.A₂ (wire₂ wq) b.2.1 (rd₂ D wq x π a b e) (op₂ D π) = true

/-- at chain 3's rounds -/
@[reducible] def Fld.strict₃ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    strictSB sMT G.c₃ G.A₃ (wire₃ wq) e.2.1 (rd₃ D wq x π a b e) (op₃ D π) = true

/-- of the openings of the external strings -/
@[reducible] def Fld.strictE : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    strictExt sMT wq.ext (readE D wq x (glue a b e).1) π.ext = true

/-- no opening that is read is missing at chain 1's rounds: its forests -/
@[reducible] def Fld.forests₁ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    forestsB G.c₁ G.A₁ (wire₁ wq) (symb₁ embS) a.2.1 (rd₁ D wq x π a b e) (op₁ D π) = some F₁

/-- chain 2's forests -/
@[reducible] def Fld.forests₂ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    forestsB G.c₂ G.A₂ (wire₂ wq) (symb₂ embS) b.2.1 (rd₂ D wq x π a b e) (op₂ D π) = some F₂

/-- chain 3's forests -/
@[reducible] def Fld.forests₃ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    forestsB G.c₃ G.A₃ (wire₃ wq) (symb₃ embS) e.2.1 (rd₃ D wq x π a b e) (op₃ D π) = some F₃

/-- the forests of the external strings -/
@[reducible] def Fld.forestsE : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    forestExt wq.ext embE cms (readE D wq x (glue a b e).1) π.ext = some Fe

/-- over the whole: at most nOpen openings in all -/
@[reducible] def Fld.count : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    (flatF F₁).length + (flatF F₂).length + (flatF F₃).length + (flatF Fe).length ≤ wq.nOpen

/-- chain 1's checks are well formed and within the depth -/
@[reducible] def Fld.fit₁ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    (flatF F₁).all (fits D wq) = true

/-- chain 2's checks are well formed and within the depth -/
@[reducible] def Fld.fit₂ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    (flatF F₂).all (fits D wq) = true

/-- chain 3's checks are well formed and within the depth -/
@[reducible] def Fld.fit₃ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    (flatF F₃).all (fits D wq) = true

/-- the external strings' checks are well formed and within the depth -/
@[reducible] def Fld.fitE : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    (flatF Fe).all (fits D wq) = true

/-- the walks of chain 1's forests run to yes in the trace -/
@[reducible] def Fld.walk₁ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    RunsIn tr (runForests (K := K) F₁ (readsF F₁)) true

/-- the walks of chain 2's forests run to yes in the trace -/
@[reducible] def Fld.walk₂ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    RunsIn tr (runForests (K := K) F₂ (readsF F₂)) true

/-- the walks of chain 3's forests run to yes in the trace -/
@[reducible] def Fld.walk₃ : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    RunsIn tr (runForests (K := K) F₃ (readsF F₃)) true

/-- the walks of the external strings' forests run to yes in the trace -/
@[reducible] def Fld.walkE : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    RunsIn tr (runForests (K := K) Fe (readsF Fe)) true

/-- the check in the request tree at the slot value runs to yes -/
@[reducible] def Fld.request : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    RunsIn tr (reqCheck (K := K) (L := L) depthReq π.rtreq π.slot π.path c π.rsalt) true

/-- over the whole: the decision, at the three chains' transcripts in a row -/
@[reducible] def Fld.accept : Stmt lam K L G Y E :=
  fun sMT sFS t D wq embS embP xin embE depthReq cms x π a b e tr F₁ F₂ F₃ Fe c =>
    D.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym) (Tr.app (s := G.c₁) (t := G.c₂ ++
      G.c₃) (tr₁ D wq π a) (Tr.app (s := G.c₂) (t := G.c₃) (tr₂ D wq π b) (tr₃ D wq π e))) = true

end Fields

/-! ## The typing, as letters -/

/-- A typing of what one fixed reading of a file gives. Pub: the public input. Dat: the reading's
data. -/
structure Typing (Pub Dat : Type) where
  I : Type
  X : Type
  lam : ℕ
  L : BatchProtocolWithLeafBody I X
  W : QueryLayout lam L
  Y : Type
  E : ExtSpec
  /-- the two lengths of salts -/
  sMT : ℕ
  sFS : ℕ
  /-- the file's rounds -/
  G : Pub → Chains
  /-- the file as it is written into the typed queries -/
  F : (u : Pub) → FileW W (G u) Y E
  /-- the outer roots, the instance, the proof string -/
  cms : Pub → Dat → List (Dig lam)
  x : Pub → Dat → Y
  prf : (u : Pub) → Dat → (F u).Prf
  /-- what the three chains yield -/
  a : (u : Pub) → Dat → Out lam (G u).c₁
  b : (u : Pub) → Dat → Out lam (G u).c₂
  e : (u : Pub) → Dat → Out lam (G u).c₃
  /-- the trace of hash calls -/
  tr : Pub → Dat → Tc W
  /-- the forests of the three chains' rounds and of the external strings -/
  F₁ : Pub → Dat → List (Forest lam L)
  F₂ : Pub → Dat → List (Forest lam L)
  F₃ : Pub → Dat → List (Forest lam L)
  Fe : Pub → Dat → List (Forest lam L)
  /-- the slot value -/
  c : Pub → Dat → Dig lam

namespace Typing
variable {Pub Dat : Type} (T : Typing Pub Dat)

/-- A statement at the typing's values. -/
@[reducible] def holds (u : Pub) (d : Dat) (S : Stmt T.lam T.W.K T.L (T.G u) T.Y T.E) : Prop :=
  S T.sMT T.sFS (T.F u).t (T.F u).D (T.F u).wq (T.F u).embS (T.F u).embP (T.F u).xin (T.F u).embE
    (T.W.dReq (T.F u).t) (T.cms u d) (T.x u d) (T.prf u d) (T.a u d) (T.b u d) (T.e u d) (T.tr u d)
    (T.F₁ u d) (T.F₂ u d) (T.F₃ u d) (T.Fe u d) (T.c u d)

/-- At every good public input and data the statement holds at the typing's values. -/
@[reducible] def Hole (Good : Pub → Dat → Prop)
    (S : (G : Chains) → Stmt T.lam T.W.K T.L G T.Y T.E) : Prop :=
  ∀ u d, Good u d → T.holds u d (S (T.G u))

end Typing

/-- **All premises of `Cuts`, as named hypotheses.** -/
structure CutHoles {Pub Dat : Type} (T : Typing Pub Dat) (Good : Pub → Dat → Prop) : Prop where
  run₁ : T.Hole Good fun _ => Fld.run₁
  run₂ : T.Hole Good fun _ => Fld.run₂
  run₃ : T.Hole Good fun _ => Fld.run₃
  joined : T.Hole Good fun _ => Fld.thirdChainEndsAtGivenValue
  salt : T.Hole Good fun _ => Fld.salt
  roots : T.Hole Good fun _ => Fld.roots
  slot : T.Hole Good fun _ => Fld.slot
  strict₁ : T.Hole Good fun _ => Fld.strict₁
  strict₂ : T.Hole Good fun _ => Fld.strict₂
  strict₃ : T.Hole Good fun _ => Fld.strict₃
  strictE : T.Hole Good fun _ => Fld.strictE
  forests₁ : T.Hole Good fun _ => Fld.forests₁
  forests₂ : T.Hole Good fun _ => Fld.forests₂
  forests₃ : T.Hole Good fun _ => Fld.forests₃
  forestsE : T.Hole Good fun _ => Fld.forestsE
  count : T.Hole Good fun _ => Fld.count
  fit₁ : T.Hole Good fun _ => Fld.fit₁
  fit₂ : T.Hole Good fun _ => Fld.fit₂
  fit₃ : T.Hole Good fun _ => Fld.fit₃
  fitE : T.Hole Good fun _ => Fld.fitE
  walk₁ : T.Hole Good fun _ => Fld.walk₁
  walk₂ : T.Hole Good fun _ => Fld.walk₂
  walk₃ : T.Hole Good fun _ => Fld.walk₃
  walkE : T.Hole Good fun _ => Fld.walkE
  request : T.Hole Good fun _ => Fld.request
  accept : T.Hole Good fun _ => Fld.accept

/-- **The named hypotheses give the yes of the compiled verifier of a file, at every good
reading.** -/
theorem yes_of_holes {Pub Dat : Type} (T : Typing Pub Dat) (Good : Pub → Dat → Prop)
    (H : CutHoles T Good) (u : Pub) (d : Dat) (g : Good u d) :
    RunsIn (T.tr u d) ((T.F u).verify T.sMT T.sFS (T.cms u d) (T.x u d) (T.prf u d)) true :=
  (T.F u).yes_of_cuts (a := T.a u d) (b := T.b u d) (e := T.e u d) (F₁ := T.F₁ u d)
    (F₂ := T.F₂ u d) (F₃ := T.F₃ u d) (Fe := T.Fe u d) (c := T.c u d)
    ⟨H.run₁ u d g, H.run₂ u d g, H.run₃ u d g, H.joined u d g, H.salt u d g, H.roots u d g, H.slot
      u d g, H.strict₁ u d g, H.strict₂ u d g, H.strict₃ u d g, H.strictE u d g, H.forests₁ u d g,
      H.forests₂ u d g, H.forests₃ u d g, H.forestsE u d g, H.count u d g, H.fit₁ u d g, H.fit₂ u
      d g, H.fit₃ u d g, H.fitE u d g, H.walk₁ u d g, H.walk₂ u d g, H.walk₃ u d g, H.walkE u d g,
      H.request u d g, H.accept u d g⟩

/-! ## The two kinds of file -/

/-- **A key file.** Where the program says yes, the fixed reading returns data at which, under the
named hypotheses, the compiled verifier of the key file says yes. -/
theorem key_yes (T : Typing KeyPub (Params.TableName × ChainsData)) (H : CutHoles T KeyGood)
    (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) :
    ∃ d, readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧
      RunsIn (T.tr ⟨F.pol, F.lay, F.KL⟩ (table, d))
        ((T.F ⟨F.pol, F.lay, F.KL⟩).verify T.sMT T.sFS (T.cms ⟨F.pol, F.lay, F.KL⟩ (table, d))
          (T.x ⟨F.pol, F.lay, F.KL⟩ (table, d)) (T.prf ⟨F.pol, F.lay, F.KL⟩ (table, d))) true := by
  have ho := port_key_chains F id table further h
  obtain ⟨_, _, d, _, _, -, -, hd, -⟩ := readKeyChains_of F table ho
  exact ⟨d, hd, yes_of_holes T KeyGood H _ _ ⟨F, rfl, rfl, rfl, ho, hd⟩⟩

/-- **A proof file.** Where the program says yes, the fixed reading returns data at which, under
the named hypotheses, the compiled verifier of the proof file says yes. -/
theorem proof_yes (T : Typing ProofPub (Params.TableName × ChainsData)) (H : CutHoles T ProofGood)
    (F : K.Files) (id : String) (table further : Params.TableName)
    (h : K.PortYesAt F id table further) :
    ∃ d, readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof = some (further, d) ∧
      RunsIn (T.tr ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d))
        ((T.F ⟨F.pol, F.lay, F.KL, F.request, F.y⟩).verify T.sMT T.sFS
          (T.cms ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d))
          (T.x ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d))
          (T.prf ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d))) true := by
  have ho := port_proof_chains F id table further h
  have he := port_entry F id table further h
  obtain ⟨_, _, _, _, _, _, d, _, _, -, -, -, -, -, -, hd, -⟩ :=
    readProofChains_of F table further he ho
  exact ⟨d, hd, yes_of_holes T ProofGood H _ _ ⟨F, table, rfl, rfl, rfl, rfl, rfl, he, ho, hd⟩⟩

end OnBytes.TieK

#print axioms OnBytes.TieK.key_yes
#print axioms OnBytes.TieK.proof_yes
