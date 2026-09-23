#!/usr/bin/env ruby
# Use the pinned Lean parser. Do not infer imports from source text.
require 'json'
require 'open3'
require 'set'

ROOT = File.expand_path('..', __dir__)
Dir.chdir(ROOT)
ENTRY = 'DecoupledConsensusStatements'
ALLOWED_PREFIXES = ['DecoupledConsensusModel.', 'DecoupledConsensusStatements.'].freeze

def allowed?(name)
  return false if name == 'DecoupledConsensusModel' # This test umbrella includes Fixture.
  return false if name.include?('Fixture')
  name == ENTRY || ALLOWED_PREFIXES.any? { |prefix| name.start_with?(prefix) }
end

if ARGV == ['--self-test']
  raise 'internal predicate accepted' if allowed?('DecoupledConsensusInternal.HealingSurface')
  raise 'fixture accepted' if allowed?('DecoupledConsensusModel.Fixture')
  raise 'test umbrella accepted' if allowed?('DecoupledConsensusModel')
  raise 'legacy props accepted' if allowed?('DecoupledConsensusInternal.Legacy.Claims')
  raise 'proof accepted' if allowed?('DecoupledConsensusProofs.ReviewTheorem')
  raise 'model rejected' unless allowed?('DecoupledConsensusModel.Execution.Run')
  raise 'generic claims rejected' unless
    allowed?('DecoupledConsensusStatements.Generic.Claims')
  raise 'concrete rejected' unless
    allowed?('DecoupledConsensusStatements.Instantiation')
  puts 'Review boundary self-test passed.'
  exit
end

abort 'Usage: ruby scripts/check-review-boundary.rb [--self-test]' unless ARGV.empty?
seen = Set.new
pending = [ENTRY]
until pending.empty?
  name = pending.pop
  next unless seen.add?(name)
  abort "Internal module in review closure: #{name}" unless allowed?(name)
  path = name.tr('.', '/') + '.lean'
  abort "Missing review source: #{path}" unless File.file?(path)
  out, err, status = Open3.capture3('lake', 'env', 'lean', '--deps-json', path)
  abort "Lean import parser failed for #{path}: #{err}\n#{out}" unless status.success?
  results = JSON.parse(out).fetch('imports')
  results.each do |result|
    abort "Lean import errors in #{path}: #{result['errors']}" unless result.fetch('errors').empty?
    result.fetch('result').fetch('imports').each do |imp|
      mod = imp.fetch('module')
      pending << mod if mod.start_with?('DecoupledConsensus')
    end
  end
end

# Every statements file must be reachable. This prevents a second, unlisted
# statement collection from being mistaken for part of the accepted surface.
Dir.glob('DecoupledConsensusStatements/**/*.lean').each do |path|
  mod = path.delete_suffix('.lean').tr('/', '.')
  abort "Unlisted statements file: #{path}" unless seen.include?(mod)
end
puts "Review boundary passed: #{seen.length} local modules; no internal predicates, proofs, or fixtures."
