---------------------------- MODULE vsfs ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Blocks,     \* e.g., {1,2,3,4,5,6,7,8}
    InodeIds    \* e.g., 0..N-1

\*NullBlock == 0
NULL == 0

\*TypeOK ==
\*    /\ freeBlocks \subseteq Blocks
\*    /\ dir \in [STRING -> InodeIds]
\*    /\ \A name \in DOMAIN dir:
\*        LET i == dir[name] IN
\*            /\ inodes[i].valid
\*            /\ ~inodes[i].isDir
\*    /\ \A i \in InodeIds:
\*        LET inode == inodes[i] IN
\*            IF inode.valid THEN
\*                /\ inode.blocks \subseteq Blocks
\*                /\ inode.blocks \cap freeBlocks = {}
\*            ELSE
\*                /\ inode.blocks = {}
\*                /\ i \notin {dir[n] : n \in DOMAIN dir}

(*--algorithm FSModel {
variables freeBlocks = Blocks \ {1},
          inodes = [i \in InodeIds |-> 
                      IF i = 0 THEN 
                          [valid |-> TRUE, isDir |-> TRUE, size |-> 0, blocks |-> {}]
                      ELSE 
                          [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]],
          dir = [n \in {} |-> 0];

define {
    MaxBlocksPerFile == 2
}

{
    while (TRUE) {
        with (op \in {"CreateFile", "WriteFile", "ReadFile", "DeleteFile"}) {
            if (op = "CreateFile") {
                with (name \in STRING) {
                    if (\E i \in InodeIds: ~inodes[i].valid /\ name \notin DOMAIN dir) {
                        with (i \in InodeIds: ~inodes[i].valid) {
                            inodes[i] := [inodes[i] EXCEPT !.valid = TRUE, !.isDir = FALSE, !.size = 0, !.blocks = {}];
                            dir[name] := i;
                        }
                    }
                }
            }
            else if (op = "WriteFile") {
                with (name \in DOMAIN dir) {
                    with (i = dir[name]) {
                        if (inodes[i].valid /\ ~inodes[i].isDir /\ Cardinality(freeBlocks) > 0 /\ Cardinality(inodes[i].blocks) < MaxBlocksPerFile) {
                            with (b \in freeBlocks) {
                                freeBlocks := freeBlocks \ {b};
                                inodes[i] := [inodes[i] EXCEPT !.blocks = @ \cup {b}, !.size = @ + 1];
                            }
                        }
                    }
                }
            }
            else if (op = "ReadFile") {
                with (name \in DOMAIN dir) {
                    with (i = dir[name]) {
                        with (offset \in 0..(inodes[i].size - 1)) {
                            skip;
                        }
                    }
                }
            }
            else if (op = "DeleteFile") {
                with (name \in DOMAIN dir) {
                    with (i = dir[name]) {
                        freeBlocks := freeBlocks \cup inodes[i].blocks;
                        inodes[i] := [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}];
                        dir := [dir EXCEPT ![name] = NULL]; \* remove entry
                    }
                }
            }
        }
    }
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ffdc07d7" /\ chksum(tla) = "cc3b2b04")
VARIABLES freeBlocks, inodes, dir

(* define statement *)
MaxBlocksPerFile == 2


vars == << freeBlocks, inodes, dir >>

Init == (* Global variables *)
        /\ freeBlocks = Blocks \ {1}
        /\ inodes = [i \in InodeIds |->
                       IF i = 0 THEN
                           [valid |-> TRUE, isDir |-> TRUE, size |-> 0, blocks |-> {}]
                       ELSE
                           [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]]
        /\ dir = [n \in {} |-> 0]

Next == \E op \in {"CreateFile", "WriteFile", "ReadFile", "DeleteFile"}:
          IF op = "CreateFile"
             THEN /\ \E name \in STRING:
                       IF \E i \in InodeIds: ~inodes[i].valid /\ name \notin DOMAIN dir
                          THEN /\ \E i \in InodeIds:
                                    /\ inodes' = [inodes EXCEPT ![i] = [inodes[i] EXCEPT !.valid = TRUE, !.isDir = FALSE, !.size = 0, !.blocks = {}]]
                                    /\ dir' = [dir EXCEPT ![name] = i]
                          ELSE /\ TRUE
                               /\ UNCHANGED << inodes, dir >>
                  /\ UNCHANGED freeBlocks
             ELSE /\ IF op = "WriteFile"
                        THEN /\ \E name \in DOMAIN dir:
                                  LET i == dir[name] IN
                                    IF inodes[i].valid /\ ~inodes[i].isDir /\ Cardinality(freeBlocks) > 0 /\ Cardinality(inodes[i].blocks) < MaxBlocksPerFile
                                       THEN /\ \E b \in freeBlocks:
                                                 /\ freeBlocks' = freeBlocks \ {b}
                                                 /\ inodes' = [inodes EXCEPT ![i] = [inodes[i] EXCEPT !.blocks = @ \cup {b}, !.size = @ + 1]]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << freeBlocks, 
                                                            inodes >>
                             /\ dir' = dir
                        ELSE /\ IF op = "ReadFile"
                                   THEN /\ \E name \in DOMAIN dir:
                                             LET i == dir[name] IN
                                               \E offset \in 0..(inodes[i].size - 1):
                                                 TRUE
                                        /\ UNCHANGED << freeBlocks, inodes, 
                                                        dir >>
                                   ELSE /\ IF op = "DeleteFile"
                                              THEN /\ \E name \in DOMAIN dir:
                                                        LET i == dir[name] IN
                                                          /\ freeBlocks' = (freeBlocks \cup inodes[i].blocks)
                                                          /\ inodes' = [inodes EXCEPT ![i] = [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]]
                                                          /\ dir' = [dir EXCEPT ![name] = NULL]
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED << freeBlocks, 
                                                                   inodes, 
                                                                   dir >>

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Jun 04 21:54:47 IDT 2025 by eitam
\* Created Wed Jun 04 20:59:19 IDT 2025 by eitam
