local overseer = require("overseer")
local actions = require "telescope.actions"
local sorters = require "telescope.sorters"
local action_state = require "telescope.actions.state"
local finders = require "telescope.finders"
local make_entry = require "telescope.make_entry"
local pickers = require "telescope.pickers"
local utils = require "telescope.utils"

local conf = require("telescope.config").values

local source_files = {}
vim.list_extend(source_files, vim.split(vim.fn.glob("dk/*.dk"), "\n"))
vim.list_extend(source_files, vim.split(vim.fn.glob("*.lean"), "\n"))
vim.list_extend(source_files, vim.split(vim.fn.glob("Dedukti/*.lean"), "\n"))

local templates = {
  ["translate"] = {
    builder = function()
      return {
        cmd = { "lake" },
        args = { "run", "trans", "Test.lean" },
        components = {
          { "restart_on_save", paths = source_files},
          "default",
        },
      }
    end,
  },
  ["translate only"] = {
    builder = function(params)
      return {
        cmd = { "lake" },
        args = { "run", "trans", "Test.lean", "--print", "--write", "--only", params.only},
        components = {
          { "restart_on_save", paths = source_files},
          "default",
        },
      }
    end,
  },
  ["check"] = {
    builder = function()
      return {
        cmd = { "lake" },
        args = { "run", "check"},
        components = {
          { "restart_on_save", paths = source_files},
          "default",
        },
      }
    end,
  }
}

local function region_to_text()
  local _, ls, cs = unpack(vim.fn.getpos('v'))
  local _, le, ce = unpack(vim.fn.getpos('.'))
  local swap = ls > le or (ls == le and cs > ce)
  ls, cs, le, ce = unpack(swap and {le, ce, ls, cs} or {ls, cs, le, ce})
  local text = vim.api.nvim_buf_get_text(0, ls-1, cs-1, le-1, ce, {})[1]
  return text
end

local curr_task, curr_task_win

local function task_split (task)
  if curr_task then
    if vim.api.nvim_win_is_valid(curr_task_win) then
      vim.api.nvim_win_close(curr_task_win, true)
    end
    overseer.run_action(curr_task, "unwatch")
    curr_task:dispose()
  end

  local main_win = vim.api.nvim_get_current_win()
  overseer.run_action(task, "open vsplit")
  curr_task_win = vim.api.nvim_get_current_win()
  vim.cmd("wincmd L")
  vim.cmd("wincmd 90|")
  vim.cmd("set winfixwidth")
  vim.cmd("set wrap")

  vim.api.nvim_set_current_win(main_win)
  curr_task = task
end


local prev_onlys_file = vim.fn.stdpath("data") .. "/" .. "prev_onlys.json"
local prev_onlys = vim.fn.filereadable(prev_onlys_file) ~= 0 and vim.fn.json_decode(vim.fn.readfile(prev_onlys_file)) or {}

local function run_only(only)
  prev_onlys[only] = os.time()
  local json = vim.fn.json_encode(prev_onlys)
  vim.fn.writefile({json}, prev_onlys_file)
  overseer.run_template({name = "translate only", params = {only = only}}, task_split)
end

local only_picker = function(opts) return pickers
    .new(opts, {
      prompt_title = "previous --only args",
      finder = finders.new_table {
        results = (function()
          local onlys = {}
          for only, _ in pairs(prev_onlys) do
            table.insert(onlys, only)
          end
          return onlys
        end)(),

        entry_maker = function(entry)
          return make_entry.set_default_entry_mt({
            value = entry,
            ordinal = entry,
            display = entry,
          })
        end
      },
      sorter = sorters.Sorter:new {
        discard = true,

        scoring_function = function(_, prompt, line)
          return -prev_onlys[line]
        end,
      },
      attach_mappings = function(prompt_bufnr)
        actions.select_default:replace(function()
          local selection = action_state.get_selected_entry()
          if selection == nil then
            utils.__warn_no_selection "--only args"
            return
          end

          actions.close(prompt_bufnr)
          local val = selection.value
          run_only(val)
        end)

        return true
      end,
    })
end

for name, template in pairs(templates) do
  template.name = name
  overseer.register_template(template)
end

vim.keymap.set("n", "<leader>tt", function () overseer.run_template({name = "translate"}, task_split) end)
vim.keymap.set("n", "<leader>tc", function () overseer.run_template({name = "check"}, task_split) end)
vim.keymap.set("n", "<leader>to", function () run_only(vim.fn.input("enter constant names (comma-separated, no whitespace): ")) end)
vim.keymap.set("v", "<leader>to", function () run_only(region_to_text()) end)
vim.keymap.set("n", "<leader>tO", function () only_picker():find() end)
