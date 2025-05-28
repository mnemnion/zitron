//! Main Executable of zitron
const std = @import("std");

test "exe mentioned" {
    std.debug.print("hello from zitron main\n", .{});
}


pub fn main() void {
    std.debug.print("zitron for great justice!\n", .{});
    std.process.exit(0);
}
