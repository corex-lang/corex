//! CoreX Stage 0 CLI Entrypoint (`corex`)
//!
//! Bootstraps the `corex` command-line interface using Zig `0.17.0` `std.process.Init`, forwarding
//! process arguments, environment variables, and buffered standard I/O streams to `cli/router.zig`.
//!
//! Performs zero heavy setup at startup; all arenas, string interners, and source maps are initialized
//! lazily inside the command router per `AGENTS.md` Section 2.

const std = @import("std");
const corex = @import("corex");

// ---------------------------------------- MAIN -----------------------------------------

/// Process entrypoint for the Stage 0 `corex` compiler and toolchain binary.
pub fn main(init: std.process.Init) !u8 {
    // [1] Collect command-line arguments after `argv[0]` into the process arena:
    const proc_arena = init.arena.allocator();
    var arg_iter = try std.process.Args.Iterator.initAllocator(init.minimal.args, proc_arena);
    defer arg_iter.deinit();

    _ = arg_iter.skip();
    var cli_args: std.ArrayList([]const u8) = .empty;
    while (arg_iter.next()) |arg_slice| {
        try cli_args.append(proc_arena, arg_slice);
    }

    // [2] Configure buffered streaming writers for `stdout` and `stderr`:
    var stdout_buf: [4096]u8 = undefined;
    var stderr_buf: [4096]u8 = undefined;
    var stdout_file_writer = std.Io.File.stdout().writerStreaming(init.io, &stdout_buf);
    var stderr_file_writer = std.Io.File.stderr().writerStreaming(init.io, &stderr_buf);

    // [3] Dispatch CLI command and flush output streams before exit:
    const exit_code = try corex.router.runCli(
        init.gpa,
        init.io,
        init.environ_map,
        cli_args.items,
        &stdout_file_writer.interface,
        &stderr_file_writer.interface,
    );
    try stdout_file_writer.interface.flush();
    try stderr_file_writer.interface.flush();
    return exit_code;
}
