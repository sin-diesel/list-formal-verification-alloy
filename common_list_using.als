module common_list_using[Time]

open list[Time]
open order[Time]

open insert[Time]
open erase[Time]

example: run {
	all t : Time - last {
		list_valid[t]
		Erase[t] or Insert[t]
	}
} for 6

assert different_operations_correct {
	all now : Time - last |
	let future = now.next | 
	{
		list_valid[now]
		Erase[now] or Insert[now]
	}
	implies list_valid[future] 
}

CheckInsert: check different_operations_correct for 5 but exactly 3 Time
