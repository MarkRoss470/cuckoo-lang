use super::*;

#[test]
fn test_make_application_stack() {
    let id_t = Identifier::dummy(0);
    let prop = TypedTerm::sort_literal(Level::zero(), Span::dummy());
    let ty = TypedTerm::sort_literal(Level::constant(1), Span::dummy());

    let f = TypedTerm::adt_constructor(
        AdtIndex(0),
        0,
        TypedTerm::make_pi_type(
            TypedBinder {
                span: Span::dummy(),
                name: Some(id_t),
                ty: ty.clone(),
            },
            TypedTerm::make_pi_type(
                TypedBinder {
                    span: Span::dummy(),
                    name: None,
                    ty: TypedTerm::bound_variable(0, Some(id_t), ty.clone(), Span::dummy()),
                },
                prop.clone(),
                Span::dummy(),
            ),
            Span::dummy(),
        ),
        LevelArgs::default(),
        Span::dummy(),
    );

    let nat = TypedTerm::adt_name(AdtIndex(1), ty.clone(), LevelArgs::default(), Span::dummy());
    let zero = TypedTerm::adt_constructor(AdtIndex(1), 0, nat.clone(), LevelArgs::default(), Span::dummy());

    let nat_to_prop = TypedTerm::make_pi_type(
        TypedBinder {
            span: Span::dummy(),
            name: None,
            ty: nat.clone(),
        },
        prop.clone(), Span::dummy()
    );

    let args = vec![nat.term.clone(), zero.term.clone()];

    assert_eq!(
        TypedTerm::make_application_stack(f.clone(), args, Span::dummy()),
        TypedTerm::make_application(
            TypedTerm::make_application(f, nat.clone(), nat_to_prop, Span::dummy()),
            zero.clone(),
            prop.clone(), Span::dummy()
        )
    );
}

#[test]
fn test_replace_binder() {
    let sort_0 = TypedTerm::sort_literal(Level::constant(0), Span::dummy());
    let adt_0 = TypedTerm::adt_name(AdtIndex(0), sort_0.clone(), LevelArgs::default(), Span::dummy());

    let id_x = Identifier::dummy(0);

    assert_eq!(
        TypedTerm::bound_variable(0, Some(id_x), sort_0.clone(), Span::dummy()).replace_binder(0, &adt_0),
        adt_0
    );

    assert_eq!(
        TypedTerm::make_pi_type(
            TypedBinder {
                span: Span::dummy(),
                name: None,
                ty: adt_0.clone()
            },
            TypedTerm::bound_variable(1, Some(id_x), sort_0.clone(), Span::dummy()), Span::dummy()
        )
        .replace_binder(0, &TypedTerm::bound_variable(1, Some(id_x), sort_0.clone(), Span::dummy())),
        TypedTerm::make_pi_type(
            TypedBinder {
                span: Span::dummy(),
                name: None,
                ty: adt_0.clone()
            },
            TypedTerm::bound_variable(2, Some(id_x), sort_0.clone(), Span::dummy()), Span::dummy()
        )
    );

    assert_eq!(
        TypedTerm::make_pi_type(
            TypedBinder {
                span: Span::dummy(),
                name: None,
                ty: adt_0.clone()
            },
            TypedTerm::bound_variable(2, Some(id_x), sort_0.clone(), Span::dummy()), Span::dummy()
        )
        .replace_binder(0, &TypedTerm::bound_variable(1, Some(id_x), sort_0.clone(), Span::dummy())),
        TypedTerm::make_pi_type(
            TypedBinder {
                span: Span::dummy(),
                name: None,
                ty: adt_0.clone()
            },
            TypedTerm::bound_variable(1, Some(id_x), sort_0, Span::dummy()), Span::dummy()
        )
    );

    // TODO: test when the variable being replaced is in the binder of a Pi / lambda
}
