use crate::transform::bound_check::BoundCheckKind::{Slice, Vector};
use crate::transform::{MirPass, MirSource};
use rustc::hir::def_id::DefId;
use rustc::hir::map::DefPathData::TypeNs;
use rustc::hir::map::DefPathData::ValueNs;
use rustc::mir::interpret::PanicInfo::BoundsCheck;
use rustc::mir::Operand::Constant;
use rustc::mir::TerminatorKind::{Assert, Call, Goto};
use rustc::mir::{BasicBlock, BasicBlockData, Body, Constant as ConstantStruct, Operand};
use rustc::ty::subst::InternalSubsts;
use rustc::ty::subst::SubstsRef;
use rustc::ty::Adt;
use rustc::ty::{Const, FnDef, TyCtxt, TyS};
use syntax_pos::Span;

pub struct BoundCheckAnalyse<'tcx, 'a> {
    body: &'a mut Body<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx, 'a> BoundCheckAnalyse<'tcx, 'a> {
    fn get_bound_checks(&'a mut self) -> Vec<BoundCheckKind<'tcx, 'a>> {
        let mut bound_checks = Vec::new();

        for block in self.body.basic_blocks_mut() {
            let terminator =
                if let Some(ref terminator) = block.terminator { terminator } else { continue };

            match &terminator.kind {
                Call { func, args: _, destination: _, cleanup: _, from_hir_call: _ } => {
                    //determin if we have a Vec index call
                    let index_func = vec![
                        "ops".to_owned(),
                        "index".to_owned(),
                        "Index".to_owned(),
                        "index".to_owned(),
                    ];
                    let index_mut_func = vec![
                        "ops".to_owned(),
                        "index".to_owned(),
                        "IndexMut".to_owned(),
                        "index_mut".to_owned(),
                    ];
                    let constant = if let Constant(constant) = func { constant } else { continue };
                    let Const { ty, .. } = constant.literal;
                    let vec_bound_check = if let FnDef(def_id, substs) = ty.kind {
                        let func_vec = self
                            .tcx
                            .def_path(def_id)
                            .data
                            .iter()
                            .map(|disambiguated_def_path_data| disambiguated_def_path_data.data)
                            .filter_map(|def_path_data| {
                                if let TypeNs(symbol) = def_path_data {
                                    Some(symbol)
                                } else if let ValueNs(symbol) = def_path_data {
                                    Some(symbol)
                                } else {
                                    None
                                }
                            })
                            .map(|x| x.with(|x| x.to_owned()))
                            .collect::<Vec<String>>();

                        //check if we have a call of index
                        //we need to check if we have a vec as first argument
                        let vec_bound_check = if index_func == func_vec {
                            println!("call index",);

                            Some(self.tcx.lang_items().index_lang_item_fn().unwrap())
                        } else if index_mut_func == func_vec {
                            Some(self.tcx.lang_items().index_mut_lang_item_fn().unwrap())
                        } else {
                            None
                        };

                        if vec_bound_check.is_some() {
                            //let (_return_type, vec) =
                            if let TyS { kind: Adt(vec, _substs), .. } = substs.type_at(0) {
                                //check if we have a index call in a vec
                                if "std::vec::Vec".to_owned() == format!("{:?}", vec) {
                                    vec_bound_check
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        unreachable!()
                    };

                    if let Some(new_def_id) = vec_bound_check {
                        let constant_struct: ConstantStruct<'tcx> =
                            if let Constant(constant_struct) = func {
                                *constant_struct.clone()
                            } else {
                                unreachable!()
                            };

                        let substs = if let ConstantStruct {
                            literal:
                                Const { ty: TyS { kind: FnDef(_id, substs), flags: _, .. }, .. },
                            ..
                        } = constant_struct
                        {
                            let index_type = substs[1];

                            let return_type =
                                if let TyS { kind: Adt(_, substs), .. } = substs.type_at(0) {
                                    substs[0]
                                } else {
                                    unreachable!()
                                };

                            let substs = InternalSubsts::for_item(
                                self.tcx,
                                new_def_id,
                                |param_def, _generic_args| match param_def.index {
                                    0 => return_type,
                                    1 => index_type,
                                    _ => unreachable!(),
                                },
                            );

                            substs
                        } else {
                            unreachable!()
                        };

                        bound_checks.push(Vector {
                            span: constant.span,
                            block,
                            substs,
                            new_def_id,
                            tcx: self.tcx,
                        });
                    }
                }

                Assert { cond: _, expected: _, msg, target, cleanup: _ } => {
                    if let BoundsCheck { .. } = msg {
                        bound_checks.push(Slice { target: target.clone(), block });
                    } else {
                        continue;
                    }
                }

                _ => continue,
            }
        }
        bound_checks
    }
}

enum BoundCheckKind<'tcx, 'a> {
    //Slice and Array
    Slice {
        target: BasicBlock,
        block: &'a mut BasicBlockData<'tcx>,
    },

    Vector {
        new_def_id: DefId,
        span: Span,
        block: &'a mut BasicBlockData<'tcx>,
        substs: SubstsRef<'tcx>,
        tcx: TyCtxt<'tcx>,
    },
}

impl<'tcx, 'a> BoundCheckKind<'tcx, 'a> {
    fn remove(self) {
        match self {
            Slice { target, block } => {
                let terminator = block.terminator_mut();

                terminator.kind = Goto { target };
            }

            Vector { new_def_id, span, substs, block, tcx } => {
                if let Call { ref mut func, .. } = block.terminator_mut().kind {
                    *func = Operand::function_handle(tcx, new_def_id, substs, span);
                } else {
                    unreachable!()
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct BoundCheckPass;

impl MirPass<'tcx> for BoundCheckPass {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, mir_source: MirSource<'tcx>, body: &mut Body<'tcx>) {
        if tcx.sess.remove_bounds_checks() {
            println!("def_id: {:?}", mir_source.def_id());

            let mut bound_check_analyse = BoundCheckAnalyse { body, tcx };

            let bound_checks = bound_check_analyse.get_bound_checks();

            let total_checks = bound_checks.len();
            let mut vec_checks = 0;
            let mut array_slice_checks = 0;

            for check in bound_checks {
                match check {
                    Vector { .. } => vec_checks += 1,
                    Slice { .. } => array_slice_checks += 1,
                }
                check.remove();
            }

            println!("Found {} Bound Checks \n    {} Vector Bound Checks \n    {} Array/Slice Bound Checks", total_checks, vec_checks, array_slice_checks);
        }
    }
}
