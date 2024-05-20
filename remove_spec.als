module erase[Time]

open list[Time]
open order[Time]

pred Erase[now: Time] {	
	some erase_item : Item |
	let future = now.next {
		erase_item.condition.now = List_Item
		erase_item.condition.future = Outside_List_Item
		erase_item not in List.items.future
		
		some all_prev[erase_item, now] implies
		let prev_item = erase_item.prev.now {
			prev_item.condition.now = List_Item
			prev_item.condition.future = List_Item
			prev_item in List.items.future	
			prev_item.prev.future = prev_item.prev.now
			prev_item.next.future = erase_item.next.now
		}
		
		some all_next[erase_item, now] implies
		let next_item = erase_item.next.now {
			next_item.condition.now = List_Item
			next_item.condition.future = List_Item
			next_item in List.items.future	
			next_item.next.future = next_item.next.now
			next_item.prev.future = erase_item.prev.now
		}

		now.items_the_same_except[erase_item.item_with_neighbours[now]]
	}
}

example: run {
	all t : Time - last {
		list_valid[t]
		Erase[t]
	}
} for 6 but exactly 4 Time

assert erasing_correct {
	all now : Time - last |
	let future = now.next | 
	{
		list_valid[now]
		Erase[now]
	}
	implies list_valid[future] 
}

CheckInsert: check erasing_correct for 5
