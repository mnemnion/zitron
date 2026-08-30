// Build script for zitron
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});

    const optimize = b.standardOptimizeOption(.{});

    //| Lemon: a faithful port of lemon.c.  This will
    //| emit precisely the same output as the original.

    const lemon_template = b.option(
        []const u8,
        "l_template",
        "A build-relative file path to a lemon template",
    ) orelse "template/lempar.c";

    const lemon_mod = b.createModule(.{
        .root_source_file = b.path("src/lemon.zig"),
        .target = target,
        .optimize = optimize,
    });
    lemon_mod.addAnonymousImport("lempar", .{ .root_source_file = b.path(lemon_template) });

    const lemon_exe = b.addExecutable(.{
        .name = "lemon",
        .root_module = lemon_mod,
    });

    b.installArtifact(lemon_exe);

    const lemon_run_cmd = b.addRunArtifact(lemon_exe);

    lemon_run_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        lemon_run_cmd.addArgs(args);
    }

    //| Zitron: the port of Lemon to emit Zig.

    // All flags which make sense are also build options.

    const z_opt = b.addOptions();
    z_opt.addOption(
        bool,
        "no_compress",
        b.option(bool, "no_compress", "Don't compress tables") orelse false,
    );
    z_opt.addOption(
        bool,
        "grammar",
        b.option(bool, "grammar", "Generate a grammar report instead of code") orelse false,
    );
    z_opt.addOption(
        bool,
        "enum_file",
        b.option(bool, "enum_file", "Generate the token enum in its own file") orelse false,
    );
    z_opt.addOption(
        bool,
        "line_numbers",
        b.option(bool, "line_numbers", "Print line number comments") orelse false,
    );
    z_opt.addOption(
        bool,
        "show_conflicts",
        b.option(bool, "show_conflicts", "Print precedence conflicts") orelse false,
    );
    z_opt.addOption(
        bool,
        "clean_exit",
        b.option(bool, "clean_exit", "Always exit with 0") orelse false,
    );
    z_opt.addOption(
        bool,
        "quiet",
        b.option(bool, "quiet", "Quiet output") orelse false,
    );
    z_opt.addOption(
        bool,
        "statistics",
        b.option(bool, "statistics", "Print statistics") orelse false,
    );
    z_opt.addOption(
        bool,
        "sql",
        b.option(bool, "sql", "Print grammar as [name].sql file") orelse false,
    );
    z_opt.addOption(
        bool,
        "only_basis",
        b.option(bool, "only_basis", "Print only the basis in report") orelse false,
    );
    z_opt.addOption(
        bool,
        "no_resort",
        b.option(bool, "no_resort", "Do not sort or renumber states") orelse false,
    );
    z_opt.addOption(
        bool,
        "unbundle",
        b.option(bool, "unbundle", "Do not bundle identical generated code blocks") orelse false,
    );
    z_opt.addOption(
        ?[]const []const u8,
        "define",
        b.option([]const []const u8, "define", "Define a preprocessor macro"),
    );

    const zitron_template = b.option(
        []const u8,
        "template",
        "A build-relative file path to a zitron template",
    ) orelse "template/ztmpl.zig";

    const zitron_mod = b.createModule(.{
        .root_source_file = b.path("src/zitron.zig"),
        .target = target,
        .optimize = optimize,
    });

    zitron_mod.addOptions("config", z_opt);

    const zitron_exe = b.addExecutable(.{
        .name = "zitron",
        .root_module = zitron_mod,
    });

    zitron_exe.root_module.addAnonymousImport("z_template", .{ .root_source_file = b.path(zitron_template) });
    zitron_exe.root_module.addOptions("config", z_opt);

    b.installArtifact(zitron_exe);

    const zitron_run_cmd = b.addRunArtifact(zitron_exe);

    zitron_run_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        zitron_run_cmd.addArgs(args);
    }
    const test_filters = b.option(
        []const []const u8,
        "test-filter",
        "Skip tests that do not match any filter",
    ) orelse &[0][]const u8{};

    const zitron_unit_tests = b.addTest(.{
        .root_module = zitron_mod,
        .filters = test_filters,
    });

    const run_zitron_unit_tests = b.addRunArtifact(zitron_unit_tests);
    const lemon_unit_tests = b.addTest(.{
        .root_module = lemon_mod,
        .filters = test_filters,
    });
    const run_lemon_unit_tests = b.addRunArtifact(lemon_unit_tests);

    const test_step = b.step("test", "Run unit tests");

    test_step.dependOn(&run_zitron_unit_tests.step);
    test_step.dependOn(&run_lemon_unit_tests.step);
    addLemonErrorPathTest(
        b,
        lemon_exe,
        target,
        optimize,
        test_step,
        "error-symbol",
        &.{"ERROR_SYMBOL"},
    );
    addLemonErrorPathTest(
        b,
        lemon_exe,
        target,
        optimize,
        test_step,
        "discard-recovery",
        &.{},
    );
    addLemonErrorPathTest(
        b,
        lemon_exe,
        target,
        optimize,
        test_step,
        "no-recovery",
        &.{"NO_RECOVERY"},
    );
    addErrorPathTest(
        b,
        zitron_exe,
        target,
        optimize,
        test_step,
        test_filters,
        "error-symbol",
        &.{"ERROR_SYMBOL"},
    );
    addErrorPathTest(
        b,
        zitron_exe,
        target,
        optimize,
        test_step,
        test_filters,
        "discard-recovery",
        &.{},
    );
    addErrorPathTest(
        b,
        zitron_exe,
        target,
        optimize,
        test_step,
        test_filters,
        "no-recovery",
        &.{"NO_RECOVERY"},
    );
    addErrorPathTest(
        b,
        zitron_exe,
        target,
        optimize,
        test_step,
        test_filters,
        "track-max-stack-depth",
        &.{"TRACK_MAX_STACK_DEPTH"},
    );
    addZitronCompressionTests(
        b,
        zitron_exe,
        target,
        optimize,
        test_step,
        test_filters,
        "fallback",
        "samples/compression_fallback.zy",
    );
    addZitronCompressionTests(
        b,
        zitron_exe,
        target,
        optimize,
        test_step,
        test_filters,
        "wildcard-reduce",
        "samples/compression_wildcard_reduce.zy",
    );
    addLemonCompressionTests(
        b,
        lemon_exe,
        target,
        optimize,
        test_step,
        "fallback",
        "samples/lemon_compression_fallback.y",
    );
    addLemonCompressionTests(
        b,
        lemon_exe,
        target,
        optimize,
        test_step,
        "wildcard-reduce",
        "samples/lemon_compression_wildcard_reduce.y",
    );

    const zitron_run_step = b.step("run", "Run zitron");
    zitron_run_step.dependOn(&zitron_run_cmd.step);

    const lemon_run_step = b.step("lemon", "Run lemon");
    lemon_run_step.dependOn(&lemon_run_cmd.step);

    const run_kcov = b.addSystemCommand(&.{
        "kcov",
        "--clean",
        "--exclude-line=unreachable,expect(false)",
    });
    run_kcov.addPrefixedDirectoryArg("--include-pattern=", b.path("."));
    const coverage_output = run_kcov.addOutputDirectoryArg(".");
    run_kcov.addArtifactArg(zitron_unit_tests);

    run_kcov.enableTestRunnerMode();

    const install_coverage = b.addInstallDirectory(.{
        .source_dir = coverage_output,
        .install_dir = .{ .custom = "coverage" },
        .install_subdir = "",
    });

    const coverage_step = b.step("coverage", "Generate coverage (kcov must be installed)");
    coverage_step.dependOn(&install_coverage.step);
}

fn addErrorPathTest(
    b: *std.Build,
    zitron_exe: *std.Build.Step.Compile,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    test_step: *std.Build.Step,
    test_filters: []const []const u8,
    name: []const u8,
    defines: []const []const u8,
) void {
    const generate = b.addRunArtifact(zitron_exe);
    generate.addArgs(&.{ "--fifo", "--quiet" });
    for (defines) |define| generate.addArgs(&.{ "-D", define });
    generate.addArg("samples/error_paths.zy");
    generate.setStdIn(.{ .lazy_path = b.path("samples/error_paths.zy") });

    const generated = generate.captureStdOut(.{
        .basename = b.fmt("error-paths-{s}.zig", .{name}),
    });
    const generated_tests = b.addTest(.{
        .name = b.fmt("error-paths-{s}", .{name}),
        .root_module = b.createModule(.{
            .root_source_file = generated,
            .target = target,
            .optimize = optimize,
        }),
        .filters = test_filters,
    });
    const run_generated_tests = b.addRunArtifact(generated_tests);
    test_step.dependOn(&run_generated_tests.step);
}

fn addZitronCompressionTests(
    b: *std.Build,
    zitron_exe: *std.Build.Step.Compile,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    test_step: *std.Build.Step,
    test_filters: []const []const u8,
    case_name: []const u8,
    grammar_path: []const u8,
) void {
    for ([_]struct { name: []const u8, option: ?[]const u8 }{
        .{ .name = "compressed", .option = null },
        .{ .name = "uncompressed", .option = "--no-compress" },
    }) |mode| {
        const name = b.fmt("compression-{s}-{s}", .{ case_name, mode.name });
        const generate = b.addRunArtifact(zitron_exe);
        generate.addArgs(&.{ "--fifo", "--quiet" });
        if (mode.option) |option| generate.addArg(option);
        generate.addArg(grammar_path);
        generate.setStdIn(.{ .lazy_path = b.path(grammar_path) });

        const generated = generate.captureStdOut(.{
            .basename = b.fmt("{s}.zig", .{name}),
        });
        const generated_tests = b.addTest(.{
            .name = name,
            .root_module = b.createModule(.{
                .root_source_file = generated,
                .target = target,
                .optimize = optimize,
            }),
            .filters = test_filters,
        });
        const run_generated_tests = b.addRunArtifact(generated_tests);
        test_step.dependOn(&run_generated_tests.step);
    }
}

fn addLemonErrorPathTest(
    b: *std.Build,
    lemon_exe: *std.Build.Step.Compile,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    test_step: *std.Build.Step,
    name: []const u8,
    defines: []const []const u8,
) void {
    const generate = b.addRunArtifact(lemon_exe);
    generate.addArg("-q");
    for (defines) |define| generate.addArg(b.fmt("-D{s}", .{define}));
    const output_dir = generate.addPrefixedOutputDirectoryArg("-d", b.fmt("lemon-error-paths-{s}", .{name}));
    generate.addFileArg(b.path("samples/lemon_error_paths.y"));

    const generated_tests = b.addExecutable(.{
        .name = b.fmt("lemon-error-paths-{s}", .{name}),
        .root_module = b.createModule(.{
            .target = target,
            .optimize = optimize,
        }),
    });
    generated_tests.root_module.addCSourceFile(.{
        .file = output_dir.path(b, "lemon_error_paths.c"),
        .flags = &.{"-std=c11"},
    });
    generated_tests.root_module.link_libc = true;

    const run_generated_tests = b.addRunArtifact(generated_tests);
    test_step.dependOn(&run_generated_tests.step);
}

fn addLemonCompressionTests(
    b: *std.Build,
    lemon_exe: *std.Build.Step.Compile,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    test_step: *std.Build.Step,
    case_name: []const u8,
    grammar_path: []const u8,
) void {
    for ([_]struct { name: []const u8, option: ?[]const u8 }{
        .{ .name = "compressed", .option = null },
        .{ .name = "uncompressed", .option = "-c" },
    }) |mode| {
        const name = b.fmt("lemon-compression-{s}-{s}", .{ case_name, mode.name });
        const generate = b.addRunArtifact(lemon_exe);
        generate.addArg("-q");
        if (mode.option) |option| generate.addArg(option);
        const output_dir = generate.addPrefixedOutputDirectoryArg("-d", name);
        generate.addFileArg(b.path(grammar_path));

        const generated_tests = b.addExecutable(.{
            .name = name,
            .root_module = b.createModule(.{
                .target = target,
                .optimize = optimize,
            }),
        });
        generated_tests.root_module.addCSourceFile(.{
            .file = output_dir.path(b, b.fmt("{s}.c", .{std.fs.path.stem(grammar_path)})),
            .flags = &.{"-std=c11"},
        });
        generated_tests.root_module.link_libc = true;

        const run_generated_tests = b.addRunArtifact(generated_tests);
        test_step.dependOn(&run_generated_tests.step);
    }
}
