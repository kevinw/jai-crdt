#import "Basic";
#import "Hash_Table";

ReplicaID :: int;

Grow_Counter :: Table(ReplicaID, int);

operator == :: (a: Grow_Counter, b: Grow_Counter) -> bool {
    if a.count != b.count
        return false;

    for a {
        b_val, found := table_find(b, it_index);
        if !found
            return false;
        if it != b_val
            return false;
    }

    return true;
}

is_zero :: (using grow_counter: Grow_Counter) -> bool {
    return grow_counter.count == 0;
}

value :: (using grow_counter: Grow_Counter) -> int {
    result := 0;
    for grow_counter {
        replica_id, local_count := it_index, it;
        result += local_count;
    }
    return result;
}

increment :: (using grow_counter: *Grow_Counter, replica_id: ReplicaID) {
    value, found := table_find(<< grow_counter, replica_id);
    if found {
        table_set(grow_counter, replica_id, value + 1);
    } else {
        table_add(grow_counter, replica_id, 1);
    }
}

merge :: (a: Grow_Counter, b: Grow_Counter) -> Grow_Counter {
    result: Grow_Counter;
    for a {
        replica_id, a_local_count := it_index, it;
        b_local_count, found := table_find(b, replica_id);
        table_set(*result, replica_id, ifx found then max(a_local_count, b_local_count) else a_local_count);
    }

    // TODO: we are doing a lot of redundant work here.
    for b {
        replica_id, b_local_count := it_index, it;
        a_local_count, found := table_find(a, replica_id);
        table_set(*result, replica_id, ifx found then max(a_local_count, b_local_count) else b_local_count);
    }

    return result;
}

Counter :: struct {
    positive: Grow_Counter;
    negative: Grow_Counter;
}

zero :: (using counter: Counter) -> bool {
    return value(positive) + value(negative) == 0;
}

value :: (using counter: Counter) -> int {
    return value(positive) - value(negative);
}

increment :: (using counter: *Counter, replica_id: ReplicaID) {
    increment(*positive, replica_id);
}

decrement :: (using counter: *Counter, replica_id: ReplicaID) {
    increment(*negative, replica_id);
}

merge :: (a: *Counter, b: *Counter) -> Counter {
    result: Counter;
    result.positive = merge(a.positive, b.positive);
    result.negative = merge(a.negative, b.negative);
    return result;
}

#scope_file

fold :: (func: $F, acc: $A, arr: []A) -> A {
    if arr.count == 0
        return acc;
    
    new_acc := func(acc, arr[0]);

    new_arr := arr;
    new_arr.data += 1;
    new_arr.count -= 1;
    return fold(func, new_acc, new_arr);
}

test_grow_counter :: () {
    gc: Grow_Counter;
    assert(is_zero(gc));
    assert(value(gc) == 0);

    replica_1: ReplicaID = 1001;
    replica_2: ReplicaID = 1002;

    increment(*gc, replica_1);
    assert(!is_zero(gc));
    assert(value(gc) == 1);

    increment(*gc, replica_2);
    assert(value(gc) == 2);

    gc2: Grow_Counter;
    assert(gc2 != gc);

    gc3 := merge(gc, gc2);
    assert(gc3 == gc);
    assert(value(gc3) == 2);
}

test_counter :: () {
    replica_1: ReplicaID = 1001;
    replica_2: ReplicaID = 1002;

    c1: Counter;
    assert(zero(c1));
    assert(value(c1) == 0);

    increment(*c1, replica_1);
    assert(value(c1) == 1);

    increment(*c1, replica_2);
    assert(value(c1) == 2);

    decrement(*c1, replica_1);
    assert(value(c1) == 1);

    decrement(*c1, replica_2);
    decrement(*c1, replica_1);
    decrement(*c1, replica_2);

    assert(value(c1) == -2);
}

#scope_export
main :: () {
    test_grow_counter();
    test_counter();

    print("OK!\n");
}
