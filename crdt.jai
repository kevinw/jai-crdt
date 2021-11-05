// Thanks https://bartoszsypytkowski.com/the-state-of-a-state-based-crdts/

#import "Basic";
#import "Hash_Table";

ReplicaID :: int;

// A monotonically increasing counter.
Grow_Counter :: Table(ReplicaID, int);

// A counter which can be incremented or decremented.
Counter :: struct {
    positive: Grow_Counter;
    negative: Grow_Counter;
}

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
    value_ptr := table_find_pointer(<< grow_counter, replica_id);
    if value_ptr != null {
        << value_ptr = (<<value_ptr) + 1;
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

merge :: (a: Counter, b: Counter) -> Counter {
    result: Counter;
    result.positive = merge(a.positive, b.positive);
    result.negative = merge(a.negative, b.negative);
    return result;
}

/* ----- */

VTime :: Grow_Counter;

Ord :: enum {
    Lt :: -1; // lower
    Eq :: 0;  // equal
    Gt :: 1;  // greater
    Cc :: 2;  // concurrent
}

compare :: (a: VTime, b: VTime) -> Ord {
    all_keys: [..]ReplicaID;
    all_keys.allocator = __temporary_allocator;
    for a
        array_add(*all_keys, it_index);
    for b
        array_add_if_unique(*all_keys, it_index);

    result: Ord = .Eq;
    for all_keys {
        va := table_find_or_default(a, it, 0);
        vb := table_find_or_default(b, it, 0);
        if      result == .Eq && va > vb result = .Gt;
        else if result == .Eq && va < vb result = .Lt;
        else if result == .Lt && va > vb result = .Cc;
        else if result == .Gt && va < vb result = .Cc;
    }
    
    return result;
}

/* ------ */

// LastWriteWinsRegister
LWWReg :: struct(V: Type) {
    Value_Type :: V;

    value: V;
    last_write_time: float64;

    zero :: LWWReg.{ .{}, 0 };
}

value :: (using reg: $T/LWWReg) -> T.Value_Type {
    return reg.value;
}

set :: (a: $T/LWWReg, b: T) -> T {
    if a.last_write_time < b.last_write_time
        return b;
    else
        return a;
}

merge :: set;

// Add-Wins Observed Removed Set

ORSet :: struct(A: Type) {
    Value_Type :: A;
    Value_Time_Table_Type :: Table(A, VTime);

    added:   Value_Time_Table_Type;
    removed: Value_Time_Table_Type;
}

value :: (using or_set: $O/ORSet, allocator := __temporary_allocator) -> []O.Value_Type {
    result: [..]O.Value_Type;
    result.allocator = allocator;

    for added {
        remove_time, found := table_find(removed, it_index);
        if found && compare(it, remove_time) == .Lt {
            // do nothing
        } else {
            array_add(*result, it_index);
        }
    }

    return result;
}

contains :: (using or_set: $O/ORSet, value: O.Value_Type) -> bool {
    added_time := table_find_pointer(added, value);
    if added_time {
        removed_time := table_find_pointer(removed, value);
        if removed_time == null || compare(<<added_time, <<removed_time) != .Lt {
            return true;
        }
    }
    return false;
}

add :: (using or_set: *$O/ORSet, replica_id: ReplicaID, value: O.Value_Type) {
    added_time := table_find_pointer(added, value);
    removed_time := table_find_pointer(removed, value);
    if added_time != null {
        increment(added_time, replica_id);
        ok, counter_to_free := table_remove(*removed, value);
        if ok uninit(*counter_to_free);
    } else if removed_time != null {
        // move the counter over to added
        increment(removed_time, replica_id);
        table_set(*added, value, <<removed_time);
        table_remove(*removed, value);
    } else {
        new_counter: VTime;
        increment(*new_counter, replica_id);
        table_add(*added, value, new_counter);
    }
}

remove_elem :: (using or_set: *$O/ORSet, replica_id: ReplicaID, value: O.Value_Type) {
    added_time := table_find_pointer(added, value);
    removed_time := table_find_pointer(removed, value);
    if added_time != null {
        // move the counter over to removed
        increment(added_time, replica_id);
        table_set(*removed, value, <<added_time);
        table_remove(*added, value);
    } else if removed_time != null {
        increment(removed_time, replica_id);
        ok, counter_to_free := table_remove(*added, value);
        if ok uninit(*counter_to_free);
    } else {
        new_counter: VTime;
        increment(*new_counter, replica_id);
        table_add(*removed, value, new_counter);
    }
}

merge :: (set1: $O/ORSet, set2: O) -> O {
    merge_keys :: (set1: O.Value_Time_Table_Type, set2: O.Value_Time_Table_Type) -> O.Value_Time_Table_Type  {
        result: O.Value_Time_Table_Type;
        for set1 {
            it_2 := table_find_pointer(set2, it_index);
            if it_2 != null {
                table_set(*result, it_index, merge(it, <<it_2));
            } else {
                table_set(*result, it_index, it);
            }
        }
        return result;
    }

    added_keys := merge_keys(set1.added, set2.added);
    removed_keys := merge_keys(set1.removed, set2.removed);

    result: O;
    for added_keys {
        removed_time := table_find_pointer(removed_keys, it_index);
        if removed_time == null || compare(it, <<removed_time) != .Lt {
            table_set(*result.added, it_index, it); // TODO: copy it
        }
    }

    for removed_keys {
        added_time := table_find_pointer(added_keys, it_index);
        if added_time == null || compare(it, <<added_time) != .Gt {
            table_set(*result.removed, it_index, it);
        }
    }

    return result;
}


#scope_file

table_find_or_default :: (table: $T, key: $K, $zero_value: $V) -> V {
    value, found := table_find(table, key);
    return ifx found value else zero_value;
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

test_orset :: () {
    replica_1: ReplicaID = 1001;
    replica_2: ReplicaID = 1002;

    ids: ORSet(int);

    assert(!contains(ids, 4));
    add(*ids, replica_1, 4);
    assert(contains(ids, 4));

    res1 := value(ids);
    assert(res1.count == 1);
    assert(res1[0] == 4);

    add(*ids, replica_2, 4);
    assert(contains(ids, 4));

    res2 := value(ids);
    assert(res2.count == 1);
    assert(res2[0] == 4);

    add(*ids, replica_2, 5);
    res3 := value(ids);
    assert(res3.count == 2);

    remove_elem(*ids, replica_1, 4);
    assert(!contains(ids, 4));
    assert(contains(ids, 5));
    assert(!contains(ids, 3));
    res4 := value(ids);
    assert(res4.count == 1 && res4[0] == 5);
    
    ids2: ORSet(int);
    ids3 := merge(ids, ids2);
    res5 := value(ids3);
    assert(res5.count == 1);
    assert(res5[0] == 5);

    // TODO: test simultaneous add and remove


    
}

#scope_export
main :: () {
    test_grow_counter();
    test_counter();
    test_orset();

    print("OK!\n");
}
