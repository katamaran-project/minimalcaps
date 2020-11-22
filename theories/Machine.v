(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Import
     Program.Tactics
     Strings.String
     ZArith.ZArith
     micromega.Lia.

From Equations Require Import
     Equations.

From MicroSail Require Import
     SemiConcrete.Outcome
     Sep.Spec
     Symbolic.Mutator
     Syntax.

From MicroSail Require Environment.
From MicroSail Require Sep.Logic.
From iris.base_logic Require lib.gen_heap lib.iprop.
From iris.base_logic Require Export invariants.
From iris.bi Require interface big_op.
From iris.proofmode Require tactics.
From stdpp Require namespaces.

Set Implicit Arguments.
Import CtxNotations.
Import EnvNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope ctx_scope.

(*** TYPES ***)

Inductive Permission : Set :=
  O | R | RW.

Inductive RegName : Set :=
  R0 | R1 | R2 | R3.

Definition LV : Set := RegName.
Definition HV : Set := RegName.
Definition RV : Set := LV + Z.

Inductive Instruction : Set :=
| jr       (lv : LV)
| jalr     (lv1 : LV) (lv2 : LV)
| j        (offset : Z)
| jal      (lv : LV) (offset : Z)
| bnez     (lv : LV) (immediate : Z)
| mv       (lv : LV) (hv : HV)
| ld       (lv : LV) (hv : HV) (immediate : Z)
| sd       (hv : HV) (lv : LV) (immediate : Z)
| addi     (lv : LV) (hv : HV) (immediate : Z)
| add      (lv1 : LV) (lv2 : LV) (lv3 : LV)
(* | lt       (lv : LV) (rv1 rv2 : RV) *)
(* | plus     (lv : LV) (rv1 rv2 : RV) *)
(* | minus    (lv : LV) (rv1 rv2 : RV) *)
(* | lea      (lv : LV) (rv : RV) *)
(* | restrict (lv : LV) (rv : RV) *)
(* | subseg   (lv : LV) (rv1 rv2 : RV) *)
(* | isptr    (lv : LV) (rv : RV) *)
(* | getp     (lv lv' : LV) *)
(* | getb     (lv lv' : LV) *)
(* | gete     (lv lv' : LV) *)
(* | geta     (lv lv' : LV) *)
(* | fail *)
| ret.

Inductive InstructionConstructor : Set :=
| kjr
| kjalr
| kj
| kjal
| kbnez
| kmv
| kld
| ksd
| kaddi
| kadd
(* | klt *)
(* | kplus *)
(* | kminus *)
(* | klea *)
(* | krestrict *)
(* | ksubseg *)
(* | kisptr *)
(* | kgetp *)
(* | kgetb *)
(* | kgete *)
(* | kgeta *)
(* | kfail *)
| kret.

Section Records.
  Local Set Primitive Projections.

  Definition Addr : Set := Z.

  Record Capability : Set :=
    MkCap
      { cap_permission : Permission;
        cap_begin      : Addr;
        cap_end        : Addr + unit;
        cap_cursor     : Addr;
      }.

End Records.

(** Enums **)
Inductive Enums : Set :=
| permission
| regname.

(** Unions **)
Inductive Unions : Set :=
| instruction.

(** Records **)
Inductive Records : Set :=
| capability.

Section TransparentObligations.
  Local Set Transparent Obligations.

  Derive NoConfusion for Capability.
  Derive NoConfusion for Permission.
  Derive NoConfusion for RegName.
  Derive NoConfusion for Enums.
  Derive NoConfusion for Unions.
  Derive NoConfusion for Records.
  Derive NoConfusion for Instruction.
  Derive NoConfusion for InstructionConstructor.

End TransparentObligations.

Derive EqDec for Permission.
Derive EqDec for Capability.
Derive EqDec for RegName.

Derive EqDec for Enums.
Derive EqDec for Unions.
Derive EqDec for Records.
Derive EqDec for Instruction.
Derive EqDec for InstructionConstructor.

Section Finite.

  Import stdpp.finite.
  Import ListNotations.

  Global Program Instance Permission_finite : Finite Permission :=
    {| enum := [O;R;RW] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance RegName_finite : Finite RegName :=
    {| enum := [R0;R1;R2;R3] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

  Global Program Instance InstructionConstructor_finite :
    Finite InstructionConstructor :=
    {| enum := [kjr;kjalr;kj;kjal;kbnez;kmv;kld;ksd;kaddi;kadd;kret] |}.
  Next Obligation.
    now apply nodup_fixed.
  Qed.
  Next Obligation.
    (* TODO: This is slow. Should be replaced by a reflective proof. *)
    intros []; apply elem_of_list_In; cbn; intuition.
  Qed.

End Finite.

Module MinCapsTypeKit <: TypeKit.

  Import stdpp.finite.

  (** ENUMS **)
  Definition 𝑬        := Enums.
  Definition 𝑬_eq_dec := Enums_eqdec.
  Definition 𝑬𝑲 (e : 𝑬) : Set :=
    match e with
    | permission => Permission
    | regname    => RegName
    end.
  Instance 𝑬𝑲_eq_dec (E : 𝑬) : EqDec (𝑬𝑲 E) :=
    ltac:(destruct E; auto with typeclass_instances).
  Instance 𝑬𝑲_finite (E : 𝑬) : Finite (𝑬𝑲 E) :=
    ltac:(destruct E; auto with typeclass_instances).

  (** UNIONS **)
  Definition 𝑼        := Unions.
  Definition 𝑼_eq_dec := Unions_eqdec.
  Definition 𝑼𝑻 (U : 𝑼) : Set :=
    match U with
    | instruction => Instruction
    end.
  Instance 𝑼𝑻_eq_dec U : EqDec (𝑼𝑻 U) :=
    ltac:(destruct U; cbn; auto with typeclass_instances).
  Definition 𝑼𝑲 (U : 𝑼) : Set :=
    match U with
    | instruction => InstructionConstructor
    end.
  Instance 𝑼𝑲_eq_dec U : EqDec (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).
  Instance 𝑼𝑲_finite U : Finite (𝑼𝑲 U) :=
    ltac:(destruct U; auto with typeclass_instances).

  (** RECORDS **)
  Definition 𝑹        := Records.
  Definition 𝑹_eq_dec := Records_eqdec.
  Definition 𝑹𝑻 (R : 𝑹) : Set :=
    match R with
    | capability => Capability
    end.
  Instance 𝑹𝑻_eq_dec R : EqDec (𝑹𝑻 R) :=
    ltac:(destruct R; auto with typeclass_instances).

  (* VARIABLES *)
  Definition 𝑿        := string.
  Definition 𝑿_eq_dec := string_dec.
  Definition 𝑺        := string.
  Definition 𝑺_eq_dec := string_dec.
  Definition 𝑿to𝑺 (x : 𝑿) : 𝑺 := x.

End MinCapsTypeKit.

(*** TERMS ***)

Module MinCapsTermKit <: TermKit.
  Module typekit := MinCapsTypeKit.
  Module Export TY := Types typekit.

  Notation ty_hv := (ty_enum regname).
  Notation ty_lv := (ty_enum regname).
  Notation ty_rv := (ty_sum (ty_enum regname) ty_int).
  Notation ty_cap := (ty_record capability).
  Notation ty_word := (ty_sum ty_int ty_cap).
  Notation ty_memval := (ty_int).
  Notation ty_addr := (ty_int).
  Notation ty_perm := (ty_enum permission).
  Notation ty_instr := (ty_union instruction).

  (** UNIONS **)
  Definition 𝑼𝑲_Ty (U : 𝑼) : 𝑼𝑲 U -> Ty :=
    match U with
    | instruction => fun K =>
      match K with
      | kjr       => ty_lv
      | kjalr     => ty_prod ty_lv ty_lv
      | kj        => ty_int
      | kjal      => ty_prod ty_lv ty_int
      | kbnez     => ty_prod ty_lv ty_int
      | kmv       => ty_prod ty_lv ty_hv
      | kld       => ty_tuple [ty_lv, ty_hv, ty_int]
      | ksd       => ty_tuple [ty_hv, ty_lv, ty_int]
      | kaddi     => ty_tuple [ty_lv, ty_hv, ty_int]
      | kadd      => ty_tuple [ty_lv, ty_lv, ty_lv]
      (* | klt       => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kplus     => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kminus    => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | klea      => ty_prod ty_lv ty_rv *)
      (* | krestrict => ty_prod ty_lv ty_rv *)
      (* | ksubseg   => ty_prod ty_lv (ty_prod ty_rv ty_rv) *)
      (* | kisptr    => ty_prod ty_lv ty_rv *)
      (* | kgetp     => ty_prod ty_lv ty_lv *)
      (* | kgetb     => ty_prod ty_lv ty_lv *)
      (* | kgete     => ty_prod ty_lv ty_lv *)
      (* | kgeta     => ty_prod ty_lv ty_lv *)
      (* | kfail     => ty_unit *)
      | kret      => ty_unit
      end
    end.

  Definition 𝑼_fold (U : 𝑼) : { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } -> 𝑼𝑻 U :=
    match U with
    | instruction => fun Kv =>
      match Kv with
      | existT kjr       lv                 => jr lv
      | existT kjalr     (lv1 , lv2)        => jalr lv1 lv2
      | existT kj        offset             => j offset
      | existT kjal      (lv , offset)      => jal lv offset
      | existT kbnez     (lv , immediate)   => bnez lv immediate
      | existT kmv       (lv , hv)          => mv lv hv
      | existT kld       (tt , lv , hv , immediate) => ld lv hv immediate
      | existT ksd       (tt , hv , lv , immediate) => sd hv lv immediate
      | existT kaddi     (tt , lv , hv , immediate) => addi lv hv immediate
      | existT kadd      (tt , lv1 , lv2 , lv3)     => add lv1 lv2 lv3
      (* | existT klt       (lv , (rv1 , rv2)) => lt lv rv1 rv2 *)
      (* | existT kplus     (lv , (rv1 , rv2)) => plus lv rv1 rv2 *)
      (* | existT kminus    (lv , (rv1 , rv2)) => minus lv rv1 rv2 *)
      (* | existT klea      (lv , rv)          => lea lv rv *)
      (* | existT krestrict (lv , rv)          => restrict lv rv *)
      (* | existT ksubseg   (lv , (rv1 , rv2)) => subseg lv rv1 rv2 *)
      (* | existT kisptr    (lv , rv)          => isptr lv rv *)
      (* | existT kgetp     (lv , lv')         => getp lv lv' *)
      (* | existT kgetb     (lv , lv')         => getb lv lv' *)
      (* | existT kgete     (lv , lv')         => gete lv lv' *)
      (* | existT kgeta     (lv , lv')         => geta lv lv' *)
      (* | existT kfail     tt                 => fail *)
      | existT kret      tt                 => ret
      end
    end.
  Definition 𝑼_unfold (U : 𝑼) : 𝑼𝑻 U -> { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) } :=
    match U as u return (𝑼𝑻 u -> {K : 𝑼𝑲 u & Lit (𝑼𝑲_Ty u K)}) with
    | instruction => fun Kv =>
      match Kv with
      | jr  lv             => existT kjr   lv
      | jalr lv1 lv2       => existT kjalr (lv1 , lv2)
      | j offset           => existT kj    offset
      | jal lv offset      => existT kjal  (lv , offset)
      | bnez lv immediate  => existT kbnez (lv , immediate)
      | mv lv hv           => existT kmv   (lv , hv)
      | ld lv hv immediate => existT kld   (tt , lv , hv , immediate)
      | sd hv lv immediate => existT ksd   (tt , hv , lv , immediate)
      | addi lv hv immediate => existT kaddi (tt , lv , hv , immediate)
      | add lv1 lv2 lv3      => existT kadd (tt , lv1 , lv2 , lv3)
      (* | lt lv rv1 rv2     => existT klt       (lv , (rv1 , rv2)) *)
      (* | plus lv rv1 rv2   => existT kplus     (lv , (rv1 , rv2)) *)
      (* | minus lv rv1 rv2  => existT kminus    (lv , (rv1 , rv2)) *)
      (* | lea lv rv         => existT klea      (lv , rv) *)
      (* | restrict lv rv    => existT krestrict (lv , rv) *)
      (* | subseg lv rv1 rv2 => existT ksubseg   (lv , (rv1 , rv2)) *)
      (* | isptr lv rv       => existT kisptr    (lv , rv) *)
      (* | getp lv lv'       => existT kgetp     (lv , lv') *)
      (* | getb lv lv'       => existT kgetb     (lv , lv') *)
      (* | gete lv lv'       => existT kgete     (lv , lv') *)
      (* | geta lv lv'       => existT kgeta     (lv , lv') *)
      (* | fail              => existT kfail     tt *)
      | ret                => existT kret  tt
      end
    end.
  Lemma 𝑼_fold_unfold : forall (U : 𝑼) (Kv: 𝑼𝑻 U),
      𝑼_fold U (𝑼_unfold U Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑼_unfold_fold : forall (U : 𝑼) (Kv: { K : 𝑼𝑲 U & Lit (𝑼𝑲_Ty U K) }),
      𝑼_unfold U (𝑼_fold U Kv) = Kv.
  Proof.
    intros [] [[] x]; cbn in x;
      repeat match goal with
             | x: unit     |- _ => destruct x
             | x: prod _ _ |- _ => destruct x
             end; auto.
  Qed.

  (** RECORDS **)
  Definition 𝑹𝑭  : Set := string.

  Definition 𝑹𝑭_Ty (R : 𝑹) : Ctx (𝑹𝑭 * Ty) :=
    match R with
    | capability => [ "cap_permission" ∶ ty_perm,
                      "cap_begin"      ∶ ty_addr,
                      "cap_end"        ∶ ty_option ty_addr,
                      "cap_cursor"     ∶ ty_addr
                    ]
    end.

  Definition 𝑹_fold (R : 𝑹) : NamedEnv Lit (𝑹𝑭_Ty R) -> 𝑹𝑻 R :=
    match R with
    | capability =>
      fun fields =>
        MkCap
          (fields ‼ "cap_permission")
          (fields ‼ "cap_begin")
          (fields ‼ "cap_end")
          (fields ‼ "cap_cursor")
    end%exp.

  Definition 𝑹_unfold (R : 𝑹) : 𝑹𝑻 R -> NamedEnv Lit (𝑹𝑭_Ty R) :=
    match R  with
    | capability =>
      fun c=>
        env_nil
          ► ("cap_permission" ∶ ty_perm            ↦ cap_permission c)
          ► ("cap_begin"      ∶ ty_addr            ↦ cap_begin c)
          ► ("cap_end"        ∶ ty_option ty_addr  ↦ cap_end c)
          ► ("cap_cursor"     ∶ ty_addr            ↦ cap_cursor c)
    end%env.
  Lemma 𝑹_fold_unfold : forall (R : 𝑹) (Kv: 𝑹𝑻 R),
      𝑹_fold R (𝑹_unfold R Kv) = Kv.
  Proof. now intros [] []. Qed.
  Lemma 𝑹_unfold_fold : forall (R : 𝑹) (Kv: NamedEnv Lit (𝑹𝑭_Ty R)),
      𝑹_unfold R (𝑹_fold R Kv) = Kv.
  (* Proof. intros []; now apply Forall_forall. Qed. *)
  Admitted.

  (** FUNCTIONS **)
  Inductive Fun : Ctx (𝑿 * Ty) -> Ty -> Set :=
  | read_reg       : Fun ["reg" ∶ ty_enum regname ] ty_word
  | read_reg_cap   : Fun ["reg" ∶ ty_enum regname ] ty_cap
  | read_reg_num   : Fun ["reg" ∶ ty_enum regname ] ty_int
  | write_reg      : Fun ["reg" ∶ ty_enum regname,
                          "w"  ∶ ty_word
                         ] ty_unit
  | next_pc        : Fun ctx_nil ty_cap
  | update_pc      : Fun ctx_nil ty_unit
  | add_pc         : Fun ["offset" ∶ ty_int] ty_unit
  | read_mem       : Fun ["a"   ∶ ty_addr ] ty_memval
  | write_mem      : Fun ["a"   ∶ ty_addr,
                          "v"   ∶ ty_memval
                         ] ty_unit
  | read_allowed   : Fun ["p"   ∶ ty_perm ] ty_bool
  | write_allowed  : Fun ["p"   ∶ ty_perm ] ty_bool
  (* | sub_perm       : Fun ["p1"  ∶ ty_perm, *)
  (*                         "p2"  ∶ ty_perm *)
  (*                        ] ty_bool *)
  | upper_bound    : Fun ["a"   ∶ ty_addr,
                          "e"   ∶ ty_option ty_addr
                         ] ty_bool
  | within_bounds  : Fun ["c"   ∶ ty_cap ] ty_bool
  | compute_rv     : Fun ["rv" ∶ ty_rv] ty_word
  | compute_rv_num : Fun ["rv" ∶ ty_rv] ty_int
  | exec_jr        : Fun ["lv" ∶ ty_lv] ty_bool
  | exec_jalr      : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv ] ty_bool
  | exec_j         : Fun ["offset" ∶ ty_int] ty_bool
  | exec_jal       : Fun ["lv" ∶ ty_lv, "offset" ∶ ty_int] ty_bool
  | exec_bnez      : Fun ["lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_mv        : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv ] ty_bool
  | exec_ld        : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_sd        : Fun ["hv" ∶ ty_hv, "lv" ∶ ty_lv, "immediate" ∶ ty_int] ty_bool
  | exec_addi      : Fun ["lv" ∶ ty_lv, "hv" ∶ ty_hv, "immediate" ∶ ty_int] ty_bool
  | exec_add       : Fun ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv] ty_bool
  | exec_ret       : Fun ε ty_bool
  | exec_instr     : Fun ["i" ∶ ty_instr] ty_bool
  | exec           : Fun ε ty_bool
  | loop           : Fun ε ty_unit
  .

  Inductive FunGhost : Ctx (𝑿 * Ty) -> Set :=
  | open_ptsreg : FunGhost ["reg" ∶ ty_enum regname]
  | close_ptsreg (R : RegName) : FunGhost ctx_nil
  .

  Inductive FunX : Ctx (𝑿 * Ty) -> Ty -> Set :=
  (* read memory *)
  | rM    : FunX ["address" ∶ ty_int] ty_int
  (* write memory *)
  | wM    : FunX ["address" ∶ ty_int, "mem_value" ∶ ty_int] ty_unit
  | dI    : FunX ["code" ∶ ty_int] ty_instr
  | ghost {Δ} (f : FunGhost Δ): FunX Δ ty_unit
  .

  Definition 𝑭  : Ctx (𝑿 * Ty) -> Ty -> Set := Fun.
  Definition 𝑭𝑿  : Ctx (𝑿 * Ty) -> Ty -> Set := FunX.

  Inductive Reg : Ty -> Set :=
  | pc   : Reg ty_cap
  | reg0 : Reg ty_word
  | reg1 : Reg ty_word
  | reg2 : Reg ty_word
  | reg3 : Reg ty_word.

  Section TransparentObligations.
    Local Set Transparent Obligations.
    Derive Signature NoConfusion for Reg.
  End TransparentObligations.

  Definition 𝑹𝑬𝑮 : Ty -> Set := Reg.
  Definition 𝑹𝑬𝑮_eq_dec : EqDec (sigT Reg).
  Proof.
    intros [? []] [? []]; cbn;
      first
        [ left; now apply eq_refl
        | right; intros e; dependent elimination e
        ].
  Defined.

End MinCapsTermKit.

(*** PROGRAM ***)

Module MinCapsProgramKit <: (ProgramKit MinCapsTermKit).
  Module Export TM := Terms MinCapsTermKit.

  Local Notation "'a'"  := (@exp_var _ "a" _ _) : exp_scope.
  Local Notation "'c'"  := (@exp_var _ "c" _ _) : exp_scope.
  Local Notation "'e'"  := (@exp_var _ "e" _ _) : exp_scope.
  Local Notation "'hv'" := (@exp_var _ "hv" _ _) : exp_scope.
  Local Notation "'rv'" := (@exp_var _ "rv" _ _) : exp_scope.
  Local Notation "'i'"  := (@exp_var _ "i" _ _) : exp_scope.
  Local Notation "'lv'" := (@exp_var _ "lv" _ _) : exp_scope.
  Local Notation "'n'"  := (@exp_var _ "n" _ _) : exn_scope.
  Local Notation "'p'"  := (@exp_var _ "p" _ _) : exp_scope.
  Local Notation "'p1'" := (@exp_var _ "p1" _ _) : exp_scope.
  Local Notation "'p2'" := (@exp_var _ "p2" _ _) : exp_scope.
  Local Notation "'q'"  := (@exp_var _ "q" _ _) : exp_scope.
  Local Notation "'r'"  := (@exp_var _ "r" _ _) : exp_scope.
  Local Notation "'w'"  := (@exp_var _ "w" _ _) : exp_scope.
  Local Notation "'x'"  := (@exp_var _ "x" _ _) : exp_scope.
  Local Notation "'immediate'" := (@exp_var _ "immediate" _ _) : exp_scope.
  Local Notation "'offset'" := (@exp_var _ "offset" _ _) : exp_scope.

  Local Notation "'c'"  := "c" : string_scope.
  Local Notation "'e'"  := "e" : string_scope.
  Local Notation "'hv'" := "hv" : string_scope.
  Local Notation "'rv'" := "rv" : string_scope.
  Local Notation "'i'"  := "i" : string_scope.
  Local Notation "'lv'" := "lv" : string_scope.
  Local Notation "'n'"  := "n" : string_scope.
  Local Notation "'p'"  := "p" : string_scope.
  Local Notation "'q'"  := "q" : string_scope.
  Local Notation "'r'"  := "r" : string_scope.
  Local Notation "'w'"  := "w" : string_scope.
  Local Notation "'immediate'" := "immediate" : string_scope.
  Local Notation "'offset'" := "offset" : string_scope.

  Notation "'callghost' f" :=
    (stm_call_external (ghost f) env_nil)
    (at level 10, f at next level) : exp_scope.

  Definition fun_read_reg : Stm ["reg" ∶ ty_enum regname ] ty_word :=
    stm_call_external (ghost open_ptsreg) [exp_var "reg"]%arg ;;
    match: exp_var "reg" in regname with
    | R0 => let: "x" := stm_read_register reg0 in callghost (close_ptsreg R0) ;; stm_exp x
    | R1 => let: "x" := stm_read_register reg1 in callghost (close_ptsreg R1) ;; stm_exp x
    | R2 => let: "x" := stm_read_register reg2 in callghost (close_ptsreg R2) ;; stm_exp x
    | R3 => let: "x" := stm_read_register reg3 in callghost (close_ptsreg R3) ;; stm_exp x
    end.

  Definition fun_read_reg_cap : Stm ["reg" ∶ ty_enum regname ] ty_cap :=
    let: w := call read_reg (exp_var "reg") in
    match: w with
    | inl i => fail "Err [read_reg_cap]: expect register to hold a capability"
    | inr c => stm_exp c
    end.

  Definition fun_read_reg_num : Stm ["reg" ∶ ty_enum regname ] ty_int :=
    let: w := call read_reg (exp_var "reg") in
    match: w with
    | inl i => stm_exp i
    | inr c => fail "Err [read_reg_num]: expect register to hold a number"
    end.

  Definition fun_write_reg : Stm ["reg" ∶ ty_enum regname,
                                  "w" ∶ ty_word
                                 ] ty_unit :=
    stm_call_external (ghost open_ptsreg) [exp_var "reg"]%arg ;;
    match: exp_var "reg" in regname with
    | R0 => let: "x" := stm_write_register reg0 (exp_var "w") in callghost (close_ptsreg R0) ;; stm_exp x
    | R1 => let: "x" := stm_write_register reg1 (exp_var "w") in callghost (close_ptsreg R1) ;; stm_exp x
    | R2 => let: "x" := stm_write_register reg2 (exp_var "w") in callghost (close_ptsreg R2) ;; stm_exp x
    | R3 => let: "x" := stm_write_register reg3 (exp_var "w") in callghost (close_ptsreg R3) ;; stm_exp x
    end ;; stm_lit ty_unit tt.

  Definition fun_next_pc : Stm ctx_nil ty_cap :=
    let: "c" := stm_read_register pc in
    stm_exp (exp_record capability
                      [ ((exp_var "c")․"cap_permission"),
                        ((exp_var "c")․"cap_begin"),
                        ((exp_var "c")․"cap_end"),
                        ((exp_var "c")․"cap_cursor") + lit_int 1
                      ]%exp%arg).

  Definition fun_update_pc : Stm ctx_nil ty_unit :=
    let: "c" := call next_pc in
    stm_write_register pc (exp_var "c") ;;
    stm_lit ty_unit tt.

  Definition fun_add_pc : Stm ["offset" ∶ ty_int ] ty_unit :=
    let: "c" := stm_read_register pc in
    stm_write_register pc
      (exp_record capability
                      [ ((exp_var "c")․"cap_permission"),
                        ((exp_var "c")․"cap_begin"),
                        ((exp_var "c")․"cap_end"),
                        ((exp_var "c")․"cap_cursor") + (exp_var "offset")
                      ]%exp%arg) ;;
    stm_lit ty_unit tt.

  Definition fun_read_allowed : Stm ["p" ∶ ty_perm] ty_bool :=
    match: p in permission with
    | R   => stm_lit ty_bool true
    | RW  => stm_lit ty_bool true
    | _   => stm_lit ty_bool false
    end.

  Definition fun_write_allowed : Stm ["p" ∶ ty_perm] ty_bool :=
    match: p in permission with
    | RW  => stm_lit ty_bool true
    | _   => stm_lit ty_bool false
    end.

  (* Definition fun_sub_perm : Stm ["p1" ∶ ty_perm, "p2" ∶ ty_perm] ty_bool := *)
  (*   match: p1 in permission with *)
  (*   | O   => stm_lit ty_bool true *)
  (*   | R   => call read_allowed p2 *)
  (*   | RW  => let: "r" := call read_allowed p2 in *)
  (*            let: "w" := call write_allowed p2 in *)
  (*            stm_exp (exp_var "r" && exp_var "w") *)
  (*   end. *)

  Definition fun_within_bounds : Stm ["c" ∶ ty_cap ] ty_bool :=
    stm_match_record capability (exp_var "c")
      (recordpat_snoc (recordpat_snoc (recordpat_snoc (recordpat_snoc recordpat_nil
      "cap_permission" "p")
      "cap_begin" "b")
      "cap_end" "e")
      "cap_cursor" "a")
      (let: "u" := call upper_bound (exp_var "a") (exp_var "e") in
       stm_exp (exp_var "u" && (exp_var "b" <= exp_var "a"))).

  Definition fun_upper_bound : Stm ["a"   ∶ ty_addr, "e"   ∶ ty_option ty_addr] ty_bool :=
    match: e with
    | inl e => stm_exp (a <= e)
    | inr "_" => stm_exp (lit_bool true)
    end.
  Section ExecStore.

    Local Notation "'perm'"   := "cap_permission" : string_scope.
    Local Notation "'cursor'" := "cap_cursor" : string_scope.

    Let cap : Ty := ty_cap.
    Let bool : Ty := ty_bool.
    Let int : Ty := ty_int.
    Let word : Ty := ty_word.

    Definition fun_exec_sd : Stm [hv ∶ ty_hv, lv ∶ ty_lv, "immediate" ∶ ty_int ] ty_bool :=
      let: "base_cap" ∶ cap  := call read_reg_cap lv in
      let: "c" ∶ cap  := stm_exp (exp_record capability
                      [ ((exp_var "base_cap")․"cap_permission"),
                        ((exp_var "base_cap")․"cap_begin"),
                        ((exp_var "base_cap")․"cap_end"),
                        ((exp_var "base_cap")․"cap_cursor") + (exp_var "immediate")
                      ]%exp%arg) in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (lit_string "Err: [exec_sd] no write permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (lit_string "Err: [exec_sd] out of bounds") ;;
      let: w ∶ int := call read_reg_num hv in
      call write_mem c․cursor w ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_ld : Stm [lv ∶ ty_lv, hv ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      let: "base_cap" ∶ cap  := call read_reg_cap hv in
      let: "c" ∶ cap  := stm_exp (exp_record capability
                      [ ((exp_var "base_cap")․"cap_permission"),
                        ((exp_var "base_cap")․"cap_begin"),
                        ((exp_var "base_cap")․"cap_end"),
                        ((exp_var "base_cap")․"cap_cursor") + (exp_var "immediate")
                      ]%exp%arg) in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (lit_string "Err: [exec_ld] no read permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (lit_string "Err: [exec_ld] out of bounds") ;;
      let: n ∶ ty_memval := call read_mem c․cursor in
      call write_reg lv (exp_inl (exp_var n)) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_addi : Stm [lv ∶ ty_lv, hv ∶ ty_hv, "immediate" ∶ ty_int ] ty_bool :=
      let: "v" ∶ int := call read_reg_num hv in
      let: "res" ∶ int := stm_exp (exp_var "v" + exp_var "immediate") in
      call write_reg lv (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_add : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv, "lv3" ∶ ty_lv ] ty_bool :=
      let: "v1" ∶ int := call read_reg_num (exp_var "lv2") in
      let: "v2" ∶ int := call read_reg_num (exp_var "lv3") in
      let: "res" ∶ int := stm_exp (exp_var "v1" + exp_var "v2") in
      call write_reg (exp_var "lv1") (exp_inl (exp_var "res")) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_compute_rv : Stm [rv ∶ ty_rv] ty_word :=
      stm_match_sum rv
                    "r" (call read_reg r)
                    "n" (stm_exp (exp_inl (exp_var n))).

    Definition fun_compute_rv_num : Stm [rv ∶ ty_rv] ty_int :=
      let: w ∶ ty_word := call compute_rv rv in
      match: w with
      | inl i => stm_exp i
      | inr c => fail "Err [read_reg_num]: expect register to hold a number"
      end.

    Definition fun_exec_ret : Stm ε ty_bool :=
      stm_exp lit_false.

    Definition fun_exec_mv : Stm [lv ∶ ty_lv, hv ∶ ty_hv] ty_bool :=
      let: w ∶ word := call read_reg (exp_var hv) in
      call write_reg lv (exp_var w) ;;
      call update_pc ;;
      stm_lit ty_bool true.

    Definition fun_exec_jr : Stm [lv ∶ ty_lv] ty_bool :=
      let: "c" ∶ ty_cap := call read_reg_cap lv in
      stm_write_register pc c ;;
      stm_lit ty_bool true.

    Definition fun_exec_jalr : Stm ["lv1" ∶ ty_lv, "lv2" ∶ ty_lv] ty_bool :=
      let: "npc" := call next_pc in
      call write_reg (exp_var "lv1") (exp_inr (exp_var "npc")) ;;
      call exec_jr (exp_var "lv2").

    Definition fun_exec_j : Stm [offset ∶ ty_int ] ty_bool :=
      call add_pc (exp_binop binop_times (exp_var offset) (lit_int 2)) ;;
      stm_lit ty_bool true.

    Definition fun_exec_jal : Stm [lv ∶ ty_lv, offset ∶ ty_int] ty_bool :=
      let: "npc" := call next_pc in
      call write_reg lv (exp_inr (exp_var "npc")) ;;
      call exec_j offset.

    Definition fun_exec_bnez : Stm [lv ∶ ty_lv, immediate ∶ ty_int ] ty_bool :=
      let: "c" ∶ ty_int := call read_reg_num (exp_var lv) in
      stm_if (exp_binop binop_eq c (lit_int 0))
             (call update_pc ;; stm_lit ty_bool true)
             (call add_pc (exp_var immediate) ;; stm_lit ty_bool true).

    Definition fun_exec_instr : Stm [i ∶ ty_instr] ty_bool :=
      stm_match_union_alt
        instruction (exp_var i)
        (fun K =>
           match K with
           | kjr   => MkAlt (pat_var lv) (call exec_jr lv)
           | kjalr => MkAlt (pat_pair "lv1" "lv2") (call exec_jalr (exp_var "lv1") (exp_var "lv2"))
           | kj    => MkAlt (pat_var offset) (call exec_j offset)
           | kjal  => MkAlt (pat_pair lv offset) (call exec_jal lv offset)
           | kbnez => MkAlt (pat_pair lv immediate) (call exec_bnez lv immediate)
           | kmv   => MkAlt (pat_pair lv hv) (call exec_mv lv hv)
           | kld   => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_ld (exp_var lv) (exp_var hv) (exp_var immediate))
           | ksd   => MkAlt (pat_tuple [hv , lv , immediate])
                            (call exec_sd (exp_var hv) (exp_var lv) (exp_var immediate))
           | kaddi => MkAlt (pat_tuple [lv , hv , immediate])
                            (call exec_addi (exp_var lv) (exp_var hv) (exp_var immediate))
           | kadd  => MkAlt (pat_tuple ["lv1" , "lv2" , "lv3"])
                            (call exec_add (exp_var "lv1") (exp_var "lv2") (exp_var "lv3"))
           | kret  => MkAlt pat_unit (call exec_ret)
           end).

    Definition fun_read_mem : Stm ["a"   ∶ ty_addr ] ty_memval :=
      callex rM a.

    Definition fun_write_mem : Stm ["a"   ∶ ty_addr, "v" ∶ ty_memval ] ty_unit :=
      callex wM a (exp_var "v").

    Definition fun_exec : Stm ε ty_bool :=
      let: "c" := stm_read_register pc in
      let: p ∶ bool := call read_allowed c․perm in
      stm_assert p (lit_string "Err: [exec_ld] no read permission") ;;
      let: q ∶ bool := call within_bounds c in
      stm_assert q (lit_string "Err: [exec_ld] out of bounds") ;;
      let: n ∶ ty_memval := call read_mem c․cursor in
      let: i ∶ ty_instr := callex dI (exp_var n) in
      call exec_instr i.

    Definition fun_loop : Stm ε ty_unit :=
      let: "r" := call exec in
      if: exp_var "r"
      then call loop
      else stm_lit ty_unit tt.

  End ExecStore.

  Program Definition Pi {Δ τ} (f : Fun Δ τ) : Stm Δ τ :=
    match f with
    | read_reg       => fun_read_reg
    | read_reg_cap   => fun_read_reg_cap
    | read_reg_num   => fun_read_reg_num
    | write_reg      => fun_write_reg
    | next_pc        => fun_next_pc
    | update_pc      => fun_update_pc
    | add_pc         => fun_add_pc
    | read_mem       => fun_read_mem
    | write_mem      => fun_write_mem
    | read_allowed   => fun_read_allowed
    | write_allowed  => fun_write_allowed
    (* | sub_perm       => fun_sub_perm *)
    | upper_bound    => fun_upper_bound
    | within_bounds  => fun_within_bounds
    | exec_jr        => fun_exec_jr
    | exec_jalr      => fun_exec_jalr
    | exec_j         => fun_exec_j
    | exec_jal       => fun_exec_jal
    | exec_bnez      => fun_exec_bnez
    | exec_mv        => fun_exec_mv
    | exec_ld        => fun_exec_ld
    | exec_sd        => fun_exec_sd
    | exec_addi      => fun_exec_addi
    | exec_add       => fun_exec_add
    | exec_ret       => fun_exec_ret
    | exec_instr     => fun_exec_instr
    | compute_rv     => fun_compute_rv
    | compute_rv_num => fun_compute_rv_num
    | exec           => fun_exec
    | loop           => fun_loop
    end.

  Definition RegStore := GenericRegStore.
  Definition read_register := generic_read_register.
  Definition write_register := generic_write_register.
  Definition read_write := generic_read_write.
  Definition read_write_distinct := generic_read_write_distinct.
  Definition write_read := generic_write_read.
  Definition write_write := generic_write_write.

  (* MEMORY *)
  Definition Memory := Addr -> Z.

  Definition fun_rM (μ : Memory) (addr : Lit ty_int) : Lit ty_int :=
    μ addr.

  Definition fun_wM (μ : Memory) (addr val : Lit ty_int) : Memory :=
    fun addr' => if Z.eqb addr addr' then val else μ addr'.

  Definition fun_dI (code : Lit ty_int) : string + Lit ty_instr :=
    (* TODO: actually decode to non-trivial instructions? *)
    inr ret.

  Inductive CallEx : forall {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) (res : string + Lit σ) (γ γ' : RegStore) (μ μ' : Memory), Prop :=
  | callex_rM {addr : Z} {γ : RegStore} {μ : Memory} :
      CallEx rM (env_snoc env_nil (_ , ty_int) addr)
             (inr (fun_rM μ addr))
             γ γ μ μ
  | callex_wM {addr val : Z} {γ : RegStore} {μ : Memory} :
      CallEx wM (env_snoc (env_snoc env_nil (_ , ty_int) addr) (_ , ty_int) val)
             (inr tt)
             γ γ μ (fun_wM μ addr val)
  | callex_dI {code : Z} {γ : RegStore} {μ : Memory} :
      CallEx dI (env_snoc env_nil (_ , ty_int) code)
             (fun_dI code)
             γ γ μ μ
  | callex_ghost {Δ} {fg : FunGhost Δ} {δ : NamedEnv Lit Δ} {γ : RegStore} {μ : Memory} :
      CallEx (ghost fg) δ (inr tt) γ γ μ μ
  .

  Definition ExternalCall := @CallEx.

  Lemma ExternalProgress {σs σ} (f : 𝑭𝑿 σs σ) (args : NamedEnv Lit σs) γ μ :
    exists γ' μ' res, ExternalCall f args res γ γ' μ μ'.
  Proof.
    destruct f; cbn.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args; repeat eexists; constructor.
    - repeat depelim args; repeat eexists; constructor.
    - repeat eexists; constructor.
  Qed.

End MinCapsProgramKit.
