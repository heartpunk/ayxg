"""Small expected-value and rejection tests for AYXG's public Python contracts."""
import pytest

from ayxg import (
    Adapter, ArraySort, BVSort, BoolSort, ControlView, Declaration,
    QFAbvArrayValue, QFAbvContext, QFAbvControlView, QFAbvExpr,
    QFAbvSemantics, QFAbvStep, QFAbvSTS, QFAbvUpdate, QFAbvValuation,
    RelationSemantics, Segment, SegmentDAG, SegmentNode, STS, TermSort, TypedExpr,
    equal_valuations, eval_expr, eval_exprs, eval_step, eval_update,
)
from ayxg.expr import ArtifactError
from ayxg.qfabv import decode_sort
from ayxg.substitution import substitute_exprs


def expr(ctx, node):
    return QFAbvExpr(ctx, decode_sort(node.sort), node)


class TestSortAndExpressionContracts:
    def test_sort_roundtrips_and_conversions(self):
        sorts = [TermSort.bool(), TermSort.bv(8), TermSort.array(3, 8)]
        for sort in sorts:
            assert TermSort.from_data(sort.to_data()) == sort
            assert decode_sort(sort).encode() == sort
        assert BoolSort().encode() == TermSort.bool()
        assert BVSort(8).encode() == TermSort.bv(8)
        assert ArraySort(3, 8).encode() == TermSort.array(3, 8)

    def test_sort_deserialization_rejects_bad_shapes_and_widths(self):
        for data in [None, {}, {"kind": "bool", "width": 1},
                     {"kind": "bv", "width": 0},
                     {"kind": "bv", "width": True},
                     {"kind": "array", "index_width": 0, "value_width": 8},
                     {"kind": "array", "index_width": 2, "value_width": -1},
                     {"kind": "future"}]:
            with pytest.raises(ArtifactError):
                TermSort.from_data(data)

    def test_declaration_roundtrip_and_identifier_rejection(self):
        declaration = Declaration("pc:main", TermSort.bv(16))
        assert Declaration.from_data(declaration.to_data()) == declaration
        for name in ["", "_bad", "bad name"]:
            with pytest.raises(ArtifactError):
                Declaration(name, TermSort.bool())

    def test_context_rejects_duplicate_names_and_bad_variables(self):
        x8, x16 = Declaration("x", TermSort.bv(8)), Declaration("x", TermSort.bv(16))
        with pytest.raises(ValueError):
            QFAbvContext((x8, x16))
        ctx = QFAbvContext((x8,))
        ctx.check_expression(TypedExpr.var("x", x8.sort))
        for node in [TypedExpr.var("missing", x8.sort), TypedExpr.var("x", x16.sort)]:
            with pytest.raises(ValueError):
                ctx.check_expression(node)
        conflict_condition = TypedExpr.equal(
            TypedExpr.var("x", TermSort.bv(8)), TypedExpr.bv_lit(8, 0))
        conflict_branch = TypedExpr.ite(conflict_condition,
                                       TypedExpr.var("x", TermSort.bv(16)),
                                       TypedExpr.var("y", TermSort.bv(16)))
        conflicting = TypedExpr.equal(conflict_branch, TypedExpr.var("z", TermSort.bv(16)))
        with pytest.raises(ArtifactError):
            ctx.check_expression(conflicting)

    def test_every_operator_roundtrips(self):
        b, w, iw = TermSort.bool(), TermSort.bv(4), TermSort.bv(2)
        a = TermSort.array(2, 4)
        x, y = TypedExpr.var("x", w), TypedExpr.var("y", w)
        p = TypedExpr.var("p", b)
        i = TypedExpr.var("i", iw)
        m = TypedExpr.var("m", a)
        c = TypedExpr.bv_lit(4, 3)
        expressions = [
            p, TypedExpr.bool_lit(True), c, TypedExpr("const_array", a, (c,)),
            TypedExpr.negate(p), TypedExpr.binary("bool_and", p, TypedExpr.bool_lit(False)),
            TypedExpr.binary("bool_or", p, TypedExpr.bool_lit(False)),
            TypedExpr.ite(p, m, TypedExpr("const_array", a, (c,))),
            TypedExpr.equal(x, y), TypedExpr.unary("bv_not", x),
            *(TypedExpr.binary(op, x, y) for op in [
                "bv_add", "bv_sub", "bv_mul", "bv_udiv", "bv_urem", "bv_and",
                "bv_or", "bv_xor", "bv_shl", "bv_lshr", "bv_ashr",
                "bv_ult", "bv_ule", "bv_slt", "bv_sle"]),
            TypedExpr.sign_extend(x, 2), TypedExpr("zero_extend", TermSort.bv(6), (x,), amount=2),
            TypedExpr.extract(x, 2, 1), TypedExpr("concat", TermSort.bv(8), (x, x)),
            TypedExpr.select(m, i), TypedExpr("store", a, (m, i, c)),
        ]
        context = QFAbvContext((Declaration("x", w), Declaration("y", w),
                                Declaration("p", b), Declaration("i", iw),
                                Declaration("m", a)))
        values = (5, 7, True, 2, QFAbvArrayValue(ArraySort(2, 4), 0, ((1, 3),)))
        state = QFAbvValuation(context, values)
        for node in expressions:
            assert TypedExpr.from_data(node.to_data()) == node
            before = eval_expr(expr(context, node), state)
            after = eval_expr(expr(context, TypedExpr.from_data(node.to_data())), state)
            assert before == after

    def test_expression_deserialization_rejects_missing_extra_and_malformed_data(self):
        valid = TypedExpr.bv_lit(4, 3).to_data()
        malformed = [
            {"sort": valid["sort"], "value": 3},
            {**valid, "unexpected": 1},
            {**valid, "op": "bv_add"},
            {**valid, "value": -1},
            {**valid, "value": True},
            {"op": "var", "sort": valid["sort"], "name": "_bad"},
            {"op": "bool_lit", "sort": {"kind": "bool"}, "value": 0},
        ]
        for data in malformed:
            with pytest.raises(ArtifactError):
                TypedExpr.from_data(data)

    def test_expression_rejects_wrong_arity_sorts_metadata_and_bounds(self):
        b, w, i = TermSort.bool(), TermSort.bv(4), TermSort.bv(2)
        x, p = TypedExpr.bv_lit(4, 1), TypedExpr.bool_lit(True)
        invalid = [
            lambda: TypedExpr("bv_add", w, (x,)),
            lambda: TypedExpr("bv_add", w, (x, p)),
            lambda: TypedExpr("ite", w, (x, x, x)),
            lambda: TypedExpr("bv_lit", w, value=16),
            lambda: TypedExpr("bv_lit", w, value=True),
            lambda: TypedExpr("zero_extend", w, (x,), amount=0),
            lambda: TypedExpr("extract", w, (x,), hi=4, lo=0),
            lambda: TypedExpr("extract", w, (x,), hi=1, lo=2),
            lambda: TypedExpr("select", w, (x, i)),
            lambda: TypedExpr("store", w, (x, x, x)),
            lambda: TypedExpr("eq", b, (x, p)),
            lambda: TypedExpr("eq", b, (TypedExpr("const_array", TermSort.array(2,4), (x,)),
                                       TypedExpr("const_array", TermSort.array(2,4), (x,)))),
            lambda: TypedExpr("bool_lit", b, value=True, name="extra"),
            lambda: TypedExpr("unknown", w),
        ]
        for build in invalid:
            with pytest.raises(ArtifactError):
                build()

    def test_constructor_helpers_and_multiroot_dag_evaluation(self):
        ctx = QFAbvContext((Declaration("x", TermSort.bv(4)),))
        x = TypedExpr.var("x", TermSort.bv(4))
        state = QFAbvValuation(ctx, (15,))
        shared = TypedExpr.binary("bv_add", x, TypedExpr.bv_lit(4, 1))
        assert eval_exprs((expr(ctx, shared), expr(ctx, shared)), state) == (0, 0)
        unchanged = substitute_exprs((shared, shared), {})
        assert unchanged[0] is shared
        assert unchanged[0] is unchanged[1]
        swapped = substitute_exprs((shared, shared), {"x": TypedExpr.bv_lit(4, 2)})
        assert swapped[0] is swapped[1]
        with pytest.raises(ArtifactError):
            substitute_exprs((x,), {"x": TypedExpr.bool_lit(True)})
        assert TypedExpr.concat_all([TypedExpr.bv_lit(2, 2), TypedExpr.bv_lit(2, 1)]).sort == TermSort.bv(4)

    def test_constructor_helpers_have_expected_nodes_and_sorts(self):
        b, w = TermSort.bool(), TermSort.bv(4)
        x, y = TypedExpr.var("x", w), TypedExpr.var("y", w)
        p, q = TypedExpr.bool_lit(True), TypedExpr.bool_lit(False)
        assert TypedExpr.var("x", w) == x
        assert TypedExpr.bool_lit(True) == p
        assert TypedExpr.bv_lit(4, 3) == TypedExpr("bv_lit", w, value=3)
        assert TypedExpr.unary("bv_not", x) == TypedExpr("bv_not", w, (x,))
        assert TypedExpr.binary("bv_add", x, y) == TypedExpr("bv_add", w, (x, y))
        assert TypedExpr.negate(p) == TypedExpr("bool_not", b, (p,))
        assert TypedExpr.conjoin(p, q, p) == TypedExpr("bool_and", b, (TypedExpr("bool_and", b, (p, q)), p))
        assert TypedExpr.disjoin(p, q, p) == TypedExpr("bool_or", b, (TypedExpr("bool_or", b, (p, q)), p))
        assert TypedExpr.equal(x, y) == TypedExpr("eq", b, (x, y))
        assert TypedExpr.not_equal(x, y) == TypedExpr("bool_not", b, (TypedExpr("eq", b, (x, y)),))
        array = TypedExpr("const_array", TermSort.array(2, 4), (x,))
        index = TypedExpr.bv_lit(2, 1)
        assert TypedExpr.select(array, index) == TypedExpr("select", w, (array, index))
        assert TypedExpr.extract(x, 3, 1) == TypedExpr("extract", TermSort.bv(3), (x,), hi=3, lo=1)
        assert TypedExpr.sign_extend(x, 2) == TypedExpr("sign_extend", TermSort.bv(6), (x,), amount=2)
        assert TypedExpr.concat_all((x, TypedExpr.bv_lit(2, 1))) == TypedExpr(
            "concat", TermSort.bv(6), (x, TypedExpr.bv_lit(2, 1)))
        assert TypedExpr.ite(p, x, y) == TypedExpr("ite", w, (p, x, y))

    def test_helpers_empty_and_nonempty_variadic_cases(self):
        p = TypedExpr.bool_lit(False)
        assert TypedExpr.conjoin().value is True
        assert TypedExpr.disjoin().value is False
        assert TypedExpr.conjoin(p, p).op == "bool_and"
        assert TypedExpr.disjoin(p, p).op == "bool_or"
        assert TypedExpr.not_equal(TypedExpr.bv_lit(2, 0), TypedExpr.bv_lit(2, 1)).op == "bool_not"
        with pytest.raises(StopIteration):
            TypedExpr.concat_all([])

    def test_eval_helpers_check_context_and_array_store_read_semantics(self):
        ctx = QFAbvContext((Declaration("x", TermSort.bv(3)),
                            Declaration("m", TermSort.array(2, 3))))
        foreign = QFAbvContext((Declaration("y", TermSort.bv(3)),
                                Declaration("m", TermSort.array(2, 3))))
        state = QFAbvValuation(ctx, (5, QFAbvArrayValue(ArraySort(2, 3), 1, ((0, 2),))))
        with pytest.raises(ValueError):
            eval_exprs((QFAbvExpr(foreign, BVSort(3), TypedExpr.var("y", TermSort.bv(3))),), state)
        x = TypedExpr.var("x", TermSort.bv(3))
        memory = TypedExpr.var("m", TermSort.array(2, 3))
        store_default = TypedExpr("store", TermSort.array(2, 3),
                                  (memory, TypedExpr.bv_lit(2, 0), TypedExpr.bv_lit(3, 1)))
        stored = eval_expr(QFAbvExpr(ctx, ArraySort(2, 3), store_default), state)
        assert stored == QFAbvArrayValue(ArraySort(2, 3), 1)
        read = TypedExpr.select(TypedExpr("store", TermSort.array(2, 3),
                                          (memory, TypedExpr.bv_lit(2, 2), x)),
                                TypedExpr.bv_lit(2, 2))
        assert eval_expr(QFAbvExpr(ctx, BVSort(3), read), state) == 5
        update = QFAbvUpdate(ctx, ctx, (QFAbvExpr(ctx, BVSort(3), x),
                                        QFAbvExpr(ctx, ArraySort(2, 3), memory)))
        with pytest.raises(ValueError):
            eval_update(update, QFAbvValuation(foreign, (5, state.values[1])))


class TestValuesAndSemanticsContracts:
    def test_array_extensional_equality_accepts_different_encodings(self):
        ctx = QFAbvContext((Declaration("m", TermSort.array(1, 2)),))
        a = QFAbvArrayValue(ArraySort(1, 2), 0, ((0, 1),))
        b = QFAbvArrayValue(ArraySort(1, 2), 1, ((1, 0),))
        assert equal_valuations(QFAbvValuation(ctx, (a,)), QFAbvValuation(ctx, (b,)))
        c = QFAbvArrayValue(ArraySort(1, 2), 2)
        assert not equal_valuations(QFAbvValuation(ctx, (a,)), QFAbvValuation(ctx, (c,)))

    def test_array_support_is_canonical_and_valuations_are_typed(self):
        sort = ArraySort(2, 3)
        QFAbvArrayValue(sort, 0, ((1, 2),))
        for entries in [((1, 2), (1, 3)), ((2, 2), (1, 3)), ((1, 0),), ((4, 1),)]:
            with pytest.raises(ValueError):
                QFAbvArrayValue(sort, 0, entries)
        ctx = QFAbvContext((Declaration("p", TermSort.bool()), Declaration("x", TermSort.bv(2))))
        with pytest.raises(ValueError):
            QFAbvValuation(ctx, (1, True))
        with pytest.raises(ValueError):
            QFAbvValuation(ctx, (True, 4))
        with pytest.raises(ValueError):
            QFAbvValuation(ctx, (True,))
        with pytest.raises(ValueError):
            QFAbvArrayValue(sort, True)
        with pytest.raises(ValueError):
            QFAbvArrayValue(sort, 0, ((1, True),))

    def test_update_and_step_constructors_reject_bad_contracts(self):
        source = QFAbvContext((Declaration("x", TermSort.bv(2)),))
        foreign = QFAbvContext((Declaration("y", TermSort.bv(2)),))
        target = QFAbvContext((Declaration("z", TermSort.bool()),))
        with pytest.raises(ValueError):
            QFAbvUpdate(source, source, ())
        with pytest.raises(ValueError):
            QFAbvUpdate(source, target, (expr(source, TypedExpr.bv_lit(2, 1)),))
        with pytest.raises(ValueError):
            QFAbvUpdate(source, source, (expr(foreign, TypedExpr.var("y", TermSort.bv(2))),))
        with pytest.raises(ValueError):
            QFAbvUpdate(source, foreign, (expr(source, TypedExpr.bv_lit(2, 1)),)).compose(
                QFAbvUpdate(source, source, (expr(source, TypedExpr.bv_lit(2, 1)),)))
        with pytest.raises(ValueError):
            QFAbvStep(expr(foreign, TypedExpr.bool_lit(True)), QFAbvUpdate.identity(source))

    def test_step_denotation_checks_guard_context_and_exact_target(self):
        ctx = QFAbvContext((Declaration("x", TermSort.bv(2)),))
        update = QFAbvUpdate.identity(ctx)
        enabled = QFAbvStep(expr(ctx, TypedExpr.bool_lit(True)), update)
        disabled = QFAbvStep(expr(ctx, TypedExpr.bool_lit(False)), update)
        state = QFAbvValuation(ctx, (1,))
        other = QFAbvValuation(ctx, (2,))
        sem = QFAbvSemantics()
        assert sem.denotes(state, enabled, state)
        assert not sem.denotes(state, enabled, other)
        assert not sem.denotes(state, disabled, state)
        foreign = QFAbvContext((Declaration("y", TermSort.bv(2)),))
        assert not sem.denotes(state, enabled, QFAbvValuation(foreign, (1,)))

    def test_sts_membership_and_control_projection(self):
        ctx = QFAbvContext((Declaration("pc", TermSort.bv(2)),))
        state = QFAbvValuation(ctx, (2,))
        step = QFAbvStep.identity(ctx)
        sts_model = QFAbvSTS(ctx, (step,))
        sts = sts_model.to_sts()
        sem = QFAbvSemantics()
        assert sts.denotes(state, step, state, sem)
        absent = QFAbvStep(expr(ctx, TypedExpr.bool_lit(True)),
                           QFAbvUpdate(ctx, ctx, (expr(ctx, TypedExpr.bv_lit(2, 1)),)))
        assert not sts.denotes(state, absent, state, sem)
        with pytest.raises(ValueError):
            QFAbvSTS(ctx, (QFAbvStep(expr(QFAbvContext(()), TypedExpr.bool_lit(True)),
                                     QFAbvUpdate(QFAbvContext(()), QFAbvContext(()), ())),))
        view = QFAbvControlView(expr(ctx, TypedExpr.var("pc", TermSort.bv(2))))
        assert eval_expr(view.projection, state) == 2
        advance = QFAbvUpdate(ctx, ctx, (expr(ctx, TypedExpr.bv_lit(2, 3)),))
        assert eval_expr(view.projection, eval_update(advance, state)) == 3
        adapter = Adapter(step)
        segment = Segment(adapter, STS((step,)), (adapter,))
        assert len(segment.body.steps) == 1

    def test_generic_sts_requires_membership_and_relation(self):
        class Semantics:
            def denotes(self, source, label, target, /):
                return target == source + label
        model = STS((1, 2))
        semantics = Semantics()
        assert model.denotes(3, 1, 4, semantics)
        assert not model.denotes(3, 1, 5, semantics)
        assert not model.denotes(3, 9, 12, semantics)

    def test_segment_dag_valid_shapes_and_rejections(self):
        shapes = [
            SegmentDAG((), ()),
            SegmentDAG((SegmentNode(0, "leaf"),), (0,)),
            SegmentDAG((SegmentNode(0, "leaf"), SegmentNode(1, "chain", (0,))), (1,)),
            SegmentDAG((SegmentNode(0, "left"), SegmentNode(1, "right"),
                        SegmentNode(2, "diamond", (0, 1))), (2,)),
            SegmentDAG((SegmentNode(0, "shared"), SegmentNode(1, "parent-a", (0,)),
                        SegmentNode(2, "parent-b", (0,))), (1, 2)),
        ]
        assert len(shapes) == 5
        assert shapes[2].nodes[0].segment != shapes[2].nodes[1].segment
        assert shapes[3].nodes[2].children == (0, 1)
        assert shapes[4].nodes[1].children == shapes[4].nodes[2].children == (0,)
        assert shapes[4].nodes[1].segment != shapes[4].nodes[2].segment
        payload = object()
        invalid = [
            (SegmentNode(0, payload), SegmentNode(0, payload)),
            (SegmentNode(0, payload, (1,)), SegmentNode(1, payload)),
            (SegmentNode(1, payload, (9,)),),
            (SegmentNode(0, payload, (0,)),),
        ]
        for nodes in invalid:
            with pytest.raises(ValueError):
                SegmentDAG(nodes, ())
        with pytest.raises(ValueError):
            SegmentDAG((SegmentNode(0, payload),), (9,))
