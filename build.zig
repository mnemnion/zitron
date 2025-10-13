// Build script for zitron
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});

    const optimize = b.standardOptimizeOption(.{});

    const lemon_template = b.option(
        []const u8,
        "l_template",
        "A build-relative file path to a lemon template",
    ) orelse "template/lempar.c";

    const lemon_exe = b.addExecutable(.{
        .name = "lemon",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lemon.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    lemon_exe.root_module.addAnonymousImport("lempar", .{ .root_source_file = b.path(lemon_template) });

    b.installArtifact(lemon_exe);

    const lemon_run_cmd = b.addRunArtifact(lemon_exe);

    lemon_run_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        lemon_run_cmd.addArgs(args);
    }

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

    const zitron_exe = b.addExecutable(.{
        .name = "zitron",
        .root_module = zitron_mod,
    });

    zitron_exe.root_module.addAnonymousImport("z_template", .{ .root_source_file = b.path(zitron_template) });

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

    const test_step = b.step("test", "Run unit tests");

    test_step.dependOn(&run_zitron_unit_tests.step);

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
