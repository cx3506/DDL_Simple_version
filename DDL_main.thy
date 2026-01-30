theory DDL_main
  imports Main
begin
 typedecl i (*Possible worlds*)
 type_synonym \<sigma> = "(i\<Rightarrow>bool)" (* propositions as sets of worlds *)
 type_synonym \<gamma> = "\<sigma>\<Rightarrow>\<sigma>"      (* modal operators *)
 type_synonym \<rho> = "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>"
 type_synonym rule = "\<sigma> set \<times> \<sigma>"

consts N_OBL:: "i\<Rightarrow>(i set) set" (* neighbourhood for obligation *)
       F:: "\<sigma> set" (* set of literals/facts *)
       R_OBL:: "rule set" (* obligation rules *)
       R_PER:: "rule set" (* permission rules *)
       R_IM:: "rule set"  (* prohibition rules *)
       sup_rel :: "(rule \<times> rule) set"     (*superiority *)
       D_plus :: "\<sigma> set"
       D_minus :: "\<sigma> set"
       D_plus_OBL :: "\<sigma> set"    (* +\<partial>_OBL *)
       D_minus_OBL :: "\<sigma> set"   (* -\<partial>_OBL *)
       is_atom :: "\<sigma> \<Rightarrow> bool"

 abbreviation DDLnot::\<gamma> ("\<^bold>\<not>_"[52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)"
 abbreviation DDLand::\<rho> (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<and> \<psi>(w)"
 abbreviation DDLtop::\<sigma> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
 abbreviation DDLbot::\<sigma> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False" 
 abbreviation DDLor::\<rho> (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<or> \<psi>(w)"   
 abbreviation DDLimp::\<rho> (infixr"\<^bold>\<rightarrow>"49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longrightarrow> \<psi>(w)"  
 abbreviation DDLequ::\<rho> (infixr"\<^bold>\<leftrightarrow>"48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w) \<longleftrightarrow> \<psi>(w)" 

 (*Def. 3*)
 abbreviation sup (infix ">r" 50) where "r1 >r r2 \<equiv> (r1, r2) \<in> sup_rel" 
 abbreviation heads_opposite :: "rule \<Rightarrow> rule \<Rightarrow> bool" where "heads_opposite r1 r2 \<equiv> (snd r2 = (\<lambda>w. \<not> (snd r1 w)))"
 abbreviation acyclic_rel :: "(rule \<times> rule) set \<Rightarrow> bool" where "acyclic_rel rel \<equiv> (\<forall>x. (x, x) \<notin> trancl rel)" 
 abbreviation Defeasible_Theory :: "bool" where
   "Defeasible_Theory \<equiv>
       (\<forall>r s. (r, s) \<in> sup_rel \<longrightarrow> heads_opposite r s) \<and>
       acyclic_rel (sup_rel)"

 (*Def. 10*)
 abbreviation DDLobl::\<gamma> ("OB") where "OB \<phi> \<equiv> (\<lambda>w. {v. \<phi> v} \<in> N_OBL w)" (*The true set ||A||*)
 abbreviation DDLper::\<gamma> ("PE") where "PE \<phi> \<equiv> (\<lambda>w. {v. \<not>\<phi> v} \<notin> N_OBL w)"
 abbreviation DDLpro::\<gamma> ("IM") where "IM \<phi> \<equiv> (\<lambda>w. {v. \<not>\<phi> v} \<in> N_OBL w)"

 (*Def. 11*)
 abbreviation coherent :: "(i \<Rightarrow> (i set) set) \<Rightarrow> bool" where "coherent N \<equiv> \<forall>w X. X \<in> N w \<longrightarrow> (UNIV - X) \<notin> N w"
 abbreviation reflexive :: "(i \<Rightarrow> (i set) set) \<Rightarrow> bool" where "reflexive N \<equiv> \<forall>w X. X \<in> N w \<longrightarrow> w \<in> X"

 (*Def. 14*)
 abbreviation Defeasible_Rule_Theory :: "bool" where "Defeasible_Rule_Theory \<equiv> Defeasible_Theory" 

end
