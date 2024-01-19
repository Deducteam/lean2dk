local overseer = require("overseer")

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
        args = { "run", "trans", "Test.lean", "--only", params.only},
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

for name, template in pairs(templates) do
  template.name = name
  overseer.register_template(template)
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

vim.keymap.set("n", "<leader>tt", function () overseer.run_template({name = "translate"}, task_split) end)
vim.keymap.set("n", "<leader>tc", function () overseer.run_template({name = "check"}, task_split) end)
vim.keymap.set("n", "<leader>to", function () overseer.run_template({name = "translate only", params = {only = vim.fn.input("enter constant names (comma-separated, no whitespace): ")}}, task_split) end)
vim.keymap.set("v", "<leader>to", function () overseer.run_template({name = "translate only", params = {only = region_to_text()}}, task_split) end)
