use super::*;
use crate::parser::ast::parse_file;
use crate::typeck::TypingEnvironment;

#[test]
fn test_make_application_stack() {
    let id_t = Identifier::dummy_val(0);
    let prop = TypedTerm::sort_literal(Level::zero());
    let ty = TypedTerm::sort_literal(Level::constant(1));

    let f = TypedTerm::adt_constructor(
        AdtIndex(0),
        0,
        TypedTerm::make_pi_type(
            TypedBinder {
                name: Some(id_t),
                ty: ty.clone(),
            },
            TypedTerm::make_pi_type(
                TypedBinder {
                    name: None,
                    ty: TypedTerm::bound_variable(0, Some(id_t), ty.clone()),
                },
                prop.clone(),
            ),
        ),
        LevelArgs::default(),
    );

    let nat = TypedTerm::adt_name(AdtIndex(1), ty.clone(), LevelArgs::default());
    let zero = TypedTerm::adt_constructor(AdtIndex(1), 0, nat.clone(), LevelArgs::default());

    let nat_to_prop = TypedTerm::make_pi_type(
        TypedBinder {
            name: None,
            ty: nat.clone(),
        },
        prop.clone(),
    );

    let args = vec![nat.term.clone(), zero.term.clone()];

    assert_eq!(
        TypedTerm::make_application_stack(f.clone(), args),
        TypedTerm::make_application(
            TypedTerm::make_application(f, nat.clone(), nat_to_prop),
            zero.clone(),
            prop.clone()
        )
    );
}

#[test]
fn test_replace_binder() {
    let sort_0 = TypedTerm::sort_literal(Level::constant(0));
    let adt_0 = TypedTerm::adt_name(AdtIndex(0), sort_0.clone(), LevelArgs::default());

    let id_x = Identifier::dummy_val(0);

    assert_eq!(
        TypedTerm::bound_variable(0, Some(id_x), sort_0.clone()).replace_binder(0, &adt_0),
        adt_0
    );

    assert_eq!(
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: adt_0.clone()
            },
            TypedTerm::bound_variable(1, Some(id_x), sort_0.clone())
        )
        .replace_binder(0, &TypedTerm::bound_variable(1, Some(id_x), sort_0.clone())),
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: adt_0.clone()
            },
            TypedTerm::bound_variable(2, Some(id_x), sort_0.clone())
        )
    );

    assert_eq!(
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: adt_0.clone()
            },
            TypedTerm::bound_variable(2, Some(id_x), sort_0.clone())
        )
        .replace_binder(0, &TypedTerm::bound_variable(1, Some(id_x), sort_0.clone())),
        TypedTerm::make_pi_type(
            TypedBinder {
                name: None,
                ty: adt_0.clone()
            },
            TypedTerm::bound_variable(1, Some(id_x), sort_0)
        )
    );

    // TODO: test when the variable being replaced is in the binder of a Pi / lambda
}
